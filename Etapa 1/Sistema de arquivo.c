#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define BLOCK_SIZE 4096
#define TOTAL_BLOCKS 16
#define MAX_CHILDREN 10
#define MAX_NAME 64
#define MAX_PATH 256

typedef enum { 
    BLOCK_FREE, 
    BLOCK_INODE_ROOT, 
    BLOCK_INODE_FILE, 
    BLOCK_DATA 
} BlockType;

typedef struct {
    BlockType type;
    char description[128];
} DiskBlock;

typedef struct FileNode {
    char name[MAX_NAME];
    int is_dir;
    size_t size;
    int inode_block;
    int data_blocks[TOTAL_BLOCKS];
    int num_data_blocks;
    char full_path[MAX_PATH];
    
    struct FileNode* parent;
    struct FileNode* children[MAX_CHILDREN];
    int child_count;
} FileNode;

DiskBlock disk[TOTAL_BLOCKS];
int free_blocks_count = TOTAL_BLOCKS;
FileNode* root_node = NULL;
FileNode* file_registry[TOTAL_BLOCKS];
int registry_count = 0;

// Gestão da Camada Física (Disco)
int allocate_block(const char* desc, BlockType type) {
    for (int i = 0; i < TOTAL_BLOCKS; i++) {
        if (disk[i].type == BLOCK_FREE) {
            disk[i].type = type;
            strncpy(disk[i].description, desc, sizeof(disk[i].description) - 1);
            free_blocks_count--;
            return i;
        }
    }
    return -1;
}

void free_block(int index) {
    if (index >= 0 && index < TOTAL_BLOCKS && disk[index].type != BLOCK_FREE) {
        disk[index].type = BLOCK_FREE;
        disk[index].description[0] = '\0';
        free_blocks_count++;
    }
}

// Helpers de Árvore e Caminhos
FileNode* create_node(const char* name, int is_dir, FileNode* parent) {
    FileNode* node = (FileNode*)calloc(1, sizeof(FileNode));
    strncpy(node->name, name, MAX_NAME - 1);
    node->is_dir = is_dir;
    node->parent = parent;
    return node;
}

void split_path(const char* path, char* parent_path, char* name) {
    char temp[MAX_PATH];
    strncpy(temp, path, MAX_PATH - 1);
    temp[MAX_PATH - 1] = '\0';
    
    char* last_slash = strrchr(temp, '/');
    if (!last_slash) {
        strcpy(parent_path, "/");
        strncpy(name, path, MAX_NAME - 1);
        return;
    }
    
    if (last_slash == temp) {
        strcpy(parent_path, "/");
    } else {
        *last_slash = '\0';
        strcpy(parent_path, temp);
    }
    strncpy(name, last_slash + 1, MAX_NAME - 1);
}

FileNode* traverse_path(const char* path) {
    if (strcmp(path, "/") == 0 || strlen(path) == 0) return root_node;
    
    char temp[MAX_PATH];
    strncpy(temp, path, MAX_PATH - 1);
    
    char* token = strtok(temp, "/");
    FileNode* curr = root_node;
    
    while (token != NULL && curr != NULL) {
        int found = 0;
        for (int i = 0; i < curr->child_count; i++) {
            if (strcmp(curr->children[i]->name, token) == 0) {
                curr = curr->children[i];
                found = 1;
                break;
            }
        }
        if (!found) return NULL;
        token = strtok(NULL, "/");
    }
    return curr;
}

// ---------------- OPERAÇÕES CRUD ----------------

// 1. CREATE (Diretórios e Ficheiros)
void mkdir_fs(const char* path) {
    char parent_path[MAX_PATH], name[MAX_NAME];
    split_path(path, parent_path, name);
    
    FileNode* parent = traverse_path(parent_path);
    if (!parent || !parent->is_dir) {
        printf("Erro: Caminho pai '%s' inexistente ou inválido.\n", parent_path);
        return;
    }
    for (int i = 0; i < parent->child_count; i++) {
        if (strcmp(parent->children[i]->name, name) == 0) {
            printf("Erro: O diretório '%s' já existe.\n", name);
            return;
        }
    }
    
    FileNode* child = create_node(name, 1, parent);
    parent->children[parent->child_count++] = child;
    printf("> mkdir %s\n", path);
}

void create_file_fs(const char* path, int size_kb) {
    size_t size_bytes = size_kb * 1024;
    char parent_path[MAX_PATH], name[MAX_NAME];
    split_path(path, parent_path, name);
    
    FileNode* parent = traverse_path(parent_path);
    if (!parent || !parent->is_dir) {
        printf("Erro: Caminho pai inválido.\n");
        return;
    }
    
    int blocks_needed = (size_bytes + BLOCK_SIZE - 1) / BLOCK_SIZE;
    if (blocks_needed + 1 > free_blocks_count) {
        printf("Erro: Espaço em disco insuficiente.\n");
        return;
    }
    
    char desc[128];
    snprintf(desc, sizeof(desc), "Arquivo '%s'", path);
    int inode_idx = allocate_block(desc, BLOCK_INODE_FILE);
    
    FileNode* child = create_node(name, 0, parent);
    child->size = size_bytes;
    child->inode_block = inode_idx;
    child->num_data_blocks = blocks_needed;
    strncpy(child->full_path, path, MAX_PATH - 1);
    
    size_t remaining = size_bytes;
    for (int i = 0; i < blocks_needed; i++) {
        size_t occupied = (remaining > BLOCK_SIZE) ? BLOCK_SIZE : remaining;
        snprintf(desc, sizeof(desc), "'%s' (Bloco %d - %zu bytes ocupados)", path, i + 1, occupied);
        child->data_blocks[i] = allocate_block(desc, BLOCK_DATA);
        remaining -= occupied;
    }
    
    parent->children[parent->child_count++] = child;
    file_registry[registry_count++] = child;
    printf("> create %s --size %dKB\n", path, size_kb);
}

// 2. READ (Visões integradas nas funções de relatório e árvore)

// 3. UPDATE (Atualizar tamanho do ficheiro e alocar/libertar blocos físicos)
void update_file_fs(const char* path, int new_size_kb) {
    FileNode* node = traverse_path(path);
    if (!node || node->is_dir) {
        printf("Erro: Ficheiro '%s' inválido ou inexistente.\n", path);
        return;
    }
    
    size_t new_size_bytes = new_size_kb * 1024;
    int new_blocks_needed = (new_size_bytes + BLOCK_SIZE - 1) / BLOCK_SIZE;
    int old_blocks = node->num_data_blocks;
    
    if (new_blocks_needed > old_blocks) {
        int diff = new_blocks_needed - old_blocks;
        if (diff > free_blocks_count) {
            printf("Erro: Espaço insuficiente para expandir '%s'.\n", path);
            return;
        }
        size_t remaining = new_size_bytes - (old_blocks * BLOCK_SIZE);
        for (int i = old_blocks; i < new_blocks_needed; i++) {
            size_t occupied = (remaining > BLOCK_SIZE) ? BLOCK_SIZE : remaining;
            char desc[128];
            snprintf(desc, sizeof(desc), "'%s' (Bloco %d - %zu bytes ocupados)", path, i + 1, occupied);
            node->data_blocks[i] = allocate_block(desc, BLOCK_DATA);
            remaining -= occupied;
        }
    } else if (new_blocks_needed < old_blocks) {
        for (int i = new_blocks_needed; i < old_blocks; i++) {
            free_block(node->data_blocks[i]);
        }
    }
    
    node->size = new_size_bytes;
    node->num_data_blocks = new_blocks_needed;
    printf("> update %s --size %dKB\n", path, new_size_kb);
}

// 4. DELETE (Remover ficheiro/diretório e desalocar blocos do disco)
void delete_fs(const char* path) {
    if (strcmp(path, "/") == 0) {
        printf("Erro: Não é possível remover o diretório raiz.\n");
        return;
    }
    
    FileNode* node = traverse_path(path);
    if (!node) {
        printf("Erro: Caminho '%s' não encontrado.\n", path);
        return;
    }
    
    if (node->is_dir && node->child_count > 0) {
        printf("Erro: O diretório '%s' não está vazio.\n", path);
        return;
    }
    
    if (!node->is_dir) {
        free_block(node->inode_block);
        for (int i = 0; i < node->num_data_blocks; i++) {
            free_block(node->data_blocks[i]);
        }
        // Remover do registo de ficheiros
        for (int i = 0; i < registry_count; i++) {
            if (file_registry[i] == node) {
                for (int j = i; j < registry_count - 1; j++) {
                    file_registry[j] = file_registry[j + 1];
                }
                registry_count--;
                break;
            }
        }
    }
    
    // Remover referência no diretório pai
    FileNode* parent = node->parent;
    if (parent) {
        for (int i = 0; i < parent->child_count; i++) {
            if (parent->children[i] == node) {
                for (int j = i; j < parent->child_count - 1; j++) {
                    parent->children[j] = parent->children[j + 1];
                }
                parent->child_count--;
                break;
            }
        }
    }
    
    free(node);
    printf("> delete %s\n", path);
}

// Exibição e Relatório
void show_tree_recursive(FileNode* node, const char* prefix, int is_root) {
    if (is_root) printf("\n[ÁRVORE DO SISTEMA DE ARQUIVOS]\n/\n");
    for (int i = 0; i < node->child_count; i++) {
        FileNode* child = node->children[i];
        int is_last = (i == node->child_count - 1);
        const char* connector = is_last ? "└── " : "├── ";
        
        if (child->is_dir) {
            printf("%s%s%s/ [DIR]\n", prefix, connector, child->name);
            char new_prefix[256];
            snprintf(new_prefix, sizeof(new_prefix), "%s%s", prefix, is_last ? "    " : "│   ");
            show_tree_recursive(child, new_prefix, 0);
        } else {
            printf("%s%s%s (%zu KB) [ARQ]\n", prefix, connector, child->name, child->size / 1024);
        }
    }
}

void print_free_range(int start, int end) {
    if (start == end) printf("Bloco %02d            : [LIVRE]\n", start);
    else printf("Bloco %02d..%02d           : [LIVRE]\n", start, end);
}

void print_fragmentation_report() {
    printf("\n--- RELATÓRIO DE FRAGMENTAÇÃO ---\n");
    if (registry_count == 0) {
        printf("Nenhum arquivo no sistema.\n");
        return;
    }
    
    for (int k = 0; k < registry_count; k++) {
        FileNode* f = file_registry[k];
        size_t real_size = f->size;
        size_t allocated_bytes = f->num_data_blocks * BLOCK_SIZE;
        size_t internal_frag = allocated_bytes - real_size;
        double perc = (internal_frag > 0) ? ((double)internal_frag / BLOCK_SIZE) * 100.0 : 0.0;
        
        printf("Tamanho Real do Arquivo '%s': %zu bytes (%zu KB)\n", f->name, real_size, real_size / 1024);
        printf("Espaço Alocado no Disco          : %zu bytes (%d blocos de %d KB)\n", allocated_bytes, f->num_data_blocks, BLOCK_SIZE / 1024);
        
        if (internal_frag > 0) {
            int last_block = f->data_blocks[f->num_data_blocks - 1];
            printf("Fragmentação Interna             : %zu bytes (%.0f%% de desperdício no Bloco %02d)\n", internal_frag, perc, last_block);
        } else {
            printf("Fragmentação Interna             : 0 bytes\n");
        }
        
        printf("Fragmentação Externa             : 0 bytes\n");
        printf("Necessidade de Compactação       : NÃO (Blocos alocados via i-node indexado)\n\n");
    }
}

void fs_status() {
    printf("\n> fs_status --details\n");
    printf("Tamanho do Bloco de Disco: %d KB | Total de Blocos: %d (%d KB)\n\n",
           BLOCK_SIZE / 1024, TOTAL_BLOCKS, (TOTAL_BLOCKS * BLOCK_SIZE) / 1024);
    printf("[MAPA DE ALOCAÇÃO DO DISCO (Indexado)]\n");
    
    int free_start = -1;
    for (int i = 0; i < TOTAL_BLOCKS; i++) {
        if (disk[i].type != BLOCK_FREE) {
            if (free_start != -1) {
                print_free_range(free_start, i - 1);
                free_start = -1;
            }
            const char* type_str = "DADO";
            if (disk[i].type == BLOCK_INODE_ROOT) type_str = "INODE_RAIZ";
            else if (disk[i].type == BLOCK_INODE_FILE) type_str = "INODE_APP";
            
            printf("Bloco %02d [%-10s] : %s\n", i, type_str, disk[i].description);
        } else {
            if (free_start == -1) free_start = i;
        }
    }
    if (free_start != -1) print_free_range(free_start, TOTAL_BLOCKS - 1);
    
    print_fragmentation_report();
}

void init_fs() {
    for (int i = 0; i < TOTAL_BLOCKS; i++) {
        disk[i].type = BLOCK_FREE;
        disk[i].description[0] = '\0';
    }
    root_node = create_node("/", 1, NULL);
    allocate_block("Diretório '/'", BLOCK_INODE_ROOT);
}

int main() {
    init_fs();
    
    // Testando o ciclo CRUD completo
    mkdir_fs("/sistema");
    mkdir_fs("/sistema/logs");
    
    create_file_fs("/sistema/logs/app.log", 10);
    create_file_fs("/sistema/logs/erro.log", 4);
    
    show_tree_recursive(root_node, "", 1);
    fs_status();
    
    // Atualiza reduzindo o espaço (liberta blocos)
    update_file_fs("/sistema/logs/app.log", 6);
    
    // Elimina o ficheiro de erro (liberta o inode e blocos de dados)
    delete_fs("/sistema/logs/erro.log");
    
    printf("\n--- APÓS UPDATE E DELETE ---\n");
    show_tree_recursive(root_node, "", 1);
    fs_status();
    
    return 0;
}