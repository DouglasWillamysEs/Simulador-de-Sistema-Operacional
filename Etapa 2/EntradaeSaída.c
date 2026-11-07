/*
 * TRABALHO INTEGRADO — Etapa 1 (Sistema de Arquivos) + Etapa 2 (E/S: SSTF e RAID 5)
 *
 * Compilar : gcc -Wall -Wextra -o trabalho trabalho_integrado_fs_es.c
 * Extras   : gcc -Wall -Wextra -DEXTRA_TESTS -o trabalho trabalho_integrado_fs_es.c
 *
 * Fluxo da integração:
 *
 *   write_file_fs()   --> blocos tocados (dir. raiz + i-node + dados)
 *                     --> blocks_to_tracks() --> fila de trilhas --> SSTF
 *
 *   write_file_raid5()--> fs_create_file() aloca i-node + blocos de dados no FS
 *                     --> os blocos de dados alocados são distribuídos no RAID 5
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <ctype.h>

#define BLOCK_SIZE           4096
#define TOTAL_BLOCKS         16     /* blocos do disco do sistema de arquivos */
#define MAX_CHILDREN         10
#define MAX_NAME             64
#define MAX_PATH             256

#define DISK_COUNT           3      /* discos físicos do RAID 5 */
#define MAX_BLOCKS_PER_DISK  16
#define MAX_REQUESTS         64

/* ============================================================================
 * ETAPA 1 — SISTEMA DE ARQUIVOS
 * ============================================================================ */

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
    size_t size;                       /* em bytes */
    int inode_block;
    int data_blocks[TOTAL_BLOCKS];
    int num_data_blocks;
    char full_path[MAX_PATH];
    char content[128];                 /* último texto gravado com write_file_fs */

    struct FileNode* parent;
    struct FileNode* children[MAX_CHILDREN];
    int child_count;
} FileNode;

/* Estado global do simulador */
DiskBlock disk[TOTAL_BLOCKS];
int free_blocks_count = TOTAL_BLOCKS;
int root_block = -1;                   /* bloco do diretório raiz */
FileNode* root_node = NULL;
FileNode* file_registry[TOTAL_BLOCKS];
int registry_count = 0;

/* Copia string garantindo o terminador '\0' */
static void safe_copy(char* dst, const char* src, size_t dst_size) {
    if (dst_size == 0) return;
    strncpy(dst, src, dst_size - 1);
    dst[dst_size - 1] = '\0';
}

/* ---------- Camada física do FS ---------- */

int allocate_block(const char* desc, BlockType type) {
    for (int i = 0; i < TOTAL_BLOCKS; i++) {
        if (disk[i].type == BLOCK_FREE) {
            disk[i].type = type;
            safe_copy(disk[i].description, desc, sizeof(disk[i].description));
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

/* ---------- Árvore e caminhos ---------- */

FileNode* create_node(const char* name, int is_dir, FileNode* parent) {
    FileNode* node = (FileNode*)calloc(1, sizeof(FileNode));
    if (!node) {
        fprintf(stderr, "Erro fatal: sem memória.\n");
        exit(1);
    }
    safe_copy(node->name, name, MAX_NAME);
    node->is_dir = is_dir;
    node->parent = parent;
    node->inode_block = -1;
    return node;
}

void free_tree(FileNode* node) {
    if (!node) return;
    for (int i = 0; i < node->child_count; i++) {
        free_tree(node->children[i]);
    }
    free(node);
}

void split_path(const char* path, char* parent_path, char* name) {
    char temp[MAX_PATH];
    safe_copy(temp, path, MAX_PATH);

    char* last_slash = strrchr(temp, '/');
    if (!last_slash) {
        strcpy(parent_path, "/");
        safe_copy(name, temp, MAX_NAME);
        return;
    }

    if (last_slash == temp) {
        strcpy(parent_path, "/");
    } else {
        *last_slash = '\0';
        safe_copy(parent_path, temp, MAX_PATH);
    }
    safe_copy(name, last_slash + 1, MAX_NAME);
}

FileNode* traverse_path(const char* path) {
    if (strcmp(path, "/") == 0 || strlen(path) == 0) return root_node;

    char temp[MAX_PATH];
    safe_copy(temp, path, MAX_PATH);

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

static bool child_exists(const FileNode* parent, const char* name) {
    for (int i = 0; i < parent->child_count; i++) {
        if (strcmp(parent->children[i]->name, name) == 0) return true;
    }
    return false;
}

/* ---------- Operações do FS ---------- */

void mkdir_fs(const char* path) {
    char parent_path[MAX_PATH], name[MAX_NAME];
    split_path(path, parent_path, name);

    if (name[0] == '\0') {
        printf("Erro: nome de diretório vazio.\n");
        return;
    }

    FileNode* parent = traverse_path(parent_path);
    if (!parent || !parent->is_dir) {
        printf("Erro: Caminho pai '%s' inexistente ou inválido.\n", parent_path);
        return;
    }

    if (child_exists(parent, name)) {
        printf("Erro: '%s' já existe.\n", name);
        return;
    }

    if (parent->child_count >= MAX_CHILDREN) {
        printf("Erro: diretório '%s' cheio (máx. %d entradas).\n", parent_path, MAX_CHILDREN);
        return;
    }

    FileNode* child = create_node(name, 1, parent);
    parent->children[parent->child_count++] = child;
    printf("> mkdir %s\n", path);
}

/* Cria o arquivo no FS (i-node + blocos de dados). Retorna o nó ou NULL. */
FileNode* fs_create_file(const char* path, int size_kb, bool echo) {
    if (size_kb <= 0) {
        printf("Erro: tamanho de arquivo inválido (%d KB).\n", size_kb);
        return NULL;
    }

    size_t size_bytes = (size_t)size_kb * 1024;
    char parent_path[MAX_PATH], name[MAX_NAME];
    split_path(path, parent_path, name);

    if (name[0] == '\0') {
        printf("Erro: nome de arquivo vazio.\n");
        return NULL;
    }

    FileNode* parent = traverse_path(parent_path);
    if (!parent || !parent->is_dir) {
        printf("Erro: Caminho pai inválido.\n");
        return NULL;
    }

    if (child_exists(parent, name)) {
        printf("Erro: '%s' já existe.\n", name);
        return NULL;
    }

    if (parent->child_count >= MAX_CHILDREN) {
        printf("Erro: diretório '%s' cheio (máx. %d entradas).\n", parent_path, MAX_CHILDREN);
        return NULL;
    }

    int blocks_needed = (int)((size_bytes + BLOCK_SIZE - 1) / BLOCK_SIZE);
    if (blocks_needed + 1 > free_blocks_count) {
        printf("Erro: Espaço em disco insuficiente.\n");
        return NULL;
    }

    char desc[128];
    snprintf(desc, sizeof(desc), "Arquivo '%s'", path);
    int inode_idx = allocate_block(desc, BLOCK_INODE_FILE);

    FileNode* child = create_node(name, 0, parent);
    child->size = size_bytes;
    child->inode_block = inode_idx;
    child->num_data_blocks = blocks_needed;
    safe_copy(child->full_path, path, MAX_PATH);

    size_t remaining = size_bytes;
    for (int i = 0; i < blocks_needed; i++) {
        size_t occupied = (remaining > BLOCK_SIZE) ? BLOCK_SIZE : remaining;
        snprintf(desc, sizeof(desc), "'%s' (Bloco %d - %zu bytes ocupados)", path, i + 1, occupied);
        child->data_blocks[i] = allocate_block(desc, BLOCK_DATA);
        remaining -= occupied;
    }

    parent->children[parent->child_count++] = child;
    file_registry[registry_count++] = child;
    if (echo) printf("> create %s --size %dKB\n", path, size_kb);
    return child;
}

void create_file_fs(const char* path, int size_kb) {
    fs_create_file(path, size_kb, true);
}

/* ---------- Exibição e relatório ---------- */

void show_tree_recursive(FileNode* node, const char* prefix, int is_root) {
    if (is_root) {
        printf("\n[ÁRVORE DO SISTEMA DE ARQUIVOS]\n/\n");
    }

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
    if (start == end) {
        printf("Bloco %02d            : [LIVRE]\n", start);
    } else {
        printf("Bloco %02d..%02d           : [LIVRE]\n", start, end);
    }
}

void print_fragmentation_report(void) {
    printf("\n--- RELATÓRIO DE FRAGMENTAÇÃO ---\n");
    if (registry_count == 0) {
        printf("Nenhum arquivo no sistema.\n");
        return;
    }

    for (int k = 0; k < registry_count; k++) {
        FileNode* f = file_registry[k];
        size_t real_size = f->size;
        size_t allocated_bytes = (size_t)f->num_data_blocks * BLOCK_SIZE;
        size_t internal_frag = allocated_bytes - real_size;
        double perc = (internal_frag > 0) ? ((double)internal_frag / BLOCK_SIZE) * 100.0 : 0.0;

        printf("Tamanho Real do Arquivo '%s': %zu bytes (%zu KB)\n", f->name, real_size, real_size / 1024);
        printf("Espaço Alocado no Disco          : %zu bytes (%d blocos de %d KB)\n",
               allocated_bytes, f->num_data_blocks, BLOCK_SIZE / 1024);

        if (internal_frag > 0) {
            int last_block = f->data_blocks[f->num_data_blocks - 1];
            printf("Fragmentação Interna             : %zu bytes (%.0f%% de desperdício no Bloco %02d)\n",
                   internal_frag, perc, last_block);
        } else {
            printf("Fragmentação Interna             : 0 bytes\n");
        }

        printf("Fragmentação Externa             : 0 bytes\n");
        printf("Necessidade de Compactação       : NÃO (Blocos alocados via i-node indexado)\n");
    }
}

void fs_status(void) {
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
    if (free_start != -1) {
        print_free_range(free_start, TOTAL_BLOCKS - 1);
    }

    print_fragmentation_report();
}

void init_fs(void) {
    for (int i = 0; i < TOTAL_BLOCKS; i++) {
        disk[i].type = BLOCK_FREE;
        disk[i].description[0] = '\0';
    }
    free_blocks_count = TOTAL_BLOCKS;
    registry_count = 0;
    root_node = create_node("/", 1, NULL);
    root_block = allocate_block("Diretório '/'", BLOCK_INODE_ROOT);
    root_node->inode_block = root_block;
}

/* ============================================================================
 * ETAPA 2.1 — INTEGRAÇÃO FS -> E/S E ESCALONAMENTO DO BRAÇO (SSTF)
 * ============================================================================ */

/* Em qual trilha física cada bloco do FS está gravado.
 * (Bloco 0 = dir. raiz, 1 = i-node do 1º arquivo, 2..4 = seus dados, ...) */
static const int block_to_track[TOTAL_BLOCKS] = {
     98, 183,  37, 122,  14,  65,  67, 124,
     21,  80, 150,   9,  45, 170, 110,  30
};

int disk_head = 53;   /* posição atual da cabeça (persiste entre operações) */

/* Converte blocos do FS em trilhas. Retorna quantas trilhas foram geradas. */
int blocks_to_tracks(const int blocks[], int n, int tracks[]) {
    int count = 0;
    for (int i = 0; i < n && count < MAX_REQUESTS; i++) {
        if (blocks[i] < 0 || blocks[i] >= TOTAL_BLOCKS) {
            printf("Aviso: bloco %d fora do disco, ignorado.\n", blocks[i]);
            continue;
        }
        tracks[count++] = block_to_track[blocks[i]];
    }
    return count;
}

/* Atende a fila por SSTF e devolve a posição final da cabeça. */
int simulate_sstf_scheduling(int initial_head, const int requests[], int num_requests) {
    if (num_requests <= 0 || num_requests > MAX_REQUESTS) {
        printf("Erro: número de requisições inválido (%d).\n", num_requests);
        return initial_head;
    }

    bool visited[MAX_REQUESTS] = { false };
    int order[MAX_REQUESTS + 1];     /* ordem de atendimento (inclui posição inicial) */
    int moves[MAX_REQUESTS];         /* deslocamento de cada passo */
    int current_pos = initial_head;
    int total_movement = 0;

    printf("[E/S] Requisições de leitura/escrita pendentes nas trilhas: [");
    for (int i = 0; i < num_requests; i++) {
        printf("%d%s", requests[i], (i == num_requests - 1) ? "" : ", ");
    }
    printf("]\nPosição atual da cabeça de leitura: Trilha %d\n\n", initial_head);
    printf("--- ESCALONAMENTO DE DISCO: SSTF (Shortest Seek Time First) ---\n");

    order[0] = current_pos;
    for (int step = 0; step < num_requests; step++) {
        int min_distance = -1;
        int next_index = -1;

        for (int j = 0; j < num_requests; j++) {
            if (visited[j]) continue;
            int dist = abs(requests[j] - current_pos);
            if (next_index == -1 || dist < min_distance) {
                min_distance = dist;
                next_index = j;
            }
        }

        visited[next_index] = true;
        moves[step] = min_distance;
        order[step + 1] = requests[next_index];
        total_movement += min_distance;
        current_pos = requests[next_index];
    }

    printf("Ordem de Atendimento : ");
    for (int i = 0; i <= num_requests; i++) {
        printf("%s%d", (i == 0) ? "" : " -> ", order[i]);
    }

    printf("\nDeslocamento da Cabeça: ");
    for (int i = 0; i < num_requests; i++) {
        printf("%s|%d-%d|", (i == 0) ? "" : " + ", order[i], order[i + 1]);
    }

    printf("\nTotal de Movimento    : ");
    for (int i = 0; i < num_requests; i++) {
        printf("%s%d", (i == 0) ? "" : " + ", moves[i]);
    }
    printf(" = %d trilhas\n", total_movement);

    return current_pos;
}

/* Envia a lista de blocos tocados por uma operação do FS ao disco. */
static void io_submit(const int blocks[], int n) {
    int tracks[MAX_REQUESTS];
    int count = blocks_to_tracks(blocks, n, tracks);
    disk_head = simulate_sstf_scheduling(disk_head, tracks, count);
}

/* write_file "texto": regrava o arquivo. Toca o diretório raiz (entrada do
 * arquivo), o i-node e todos os blocos de dados. */
void write_file_fs(const char* path, const char* text) {
    printf("> write_file %s \"%s\"\n", path, text);

    FileNode* f = traverse_path(path);
    if (!f || f->is_dir) {
        printf("Erro: arquivo '%s' inexistente.\n", path);
        return;
    }
    safe_copy(f->content, text, sizeof(f->content));

    int blocks[TOTAL_BLOCKS + 2];
    int n = 0;
    blocks[n++] = root_block;
    blocks[n++] = f->inode_block;
    for (int i = 0; i < f->num_data_blocks; i++) {
        blocks[n++] = f->data_blocks[i];
    }
    io_submit(blocks, n);
}

/* read_file: lê o i-node e os blocos de dados (não altera o diretório). */
void read_file_fs(const char* path) {
    printf("> read_file %s\n", path);

    FileNode* f = traverse_path(path);
    if (!f || f->is_dir) {
        printf("Erro: arquivo '%s' inexistente.\n", path);
        return;
    }

    int blocks[TOTAL_BLOCKS + 2];
    int n = 0;
    blocks[n++] = f->inode_block;
    for (int i = 0; i < f->num_data_blocks; i++) {
        blocks[n++] = f->data_blocks[i];
    }
    io_submit(blocks, n);
    printf("Conteúdo lido: \"%s\"\n", f->content[0] ? f->content : "(vazio)");
}

/* ============================================================================
 * ETAPA 2.2 — GRAVAÇÃO FÍSICA E RECUPERAÇÃO EM ARRANJO RAID 5
 * ============================================================================
 * Cada "stripe" ocupa o mesmo índice de bloco físico em todos os discos.
 * A paridade ROTACIONA entre os discos (stripe 0 -> último disco, stripe 1 ->
 * penúltimo, ...). Cada arquivo começa em um stripe novo.
 */

typedef struct {
    unsigned char content[BLOCK_SIZE];
    bool is_parity;
    bool occupied;
    int  file_block;      /* nº do bloco dentro do arquivo (1..n); 0 se paridade/vazio */
    char label[128];
} PhysicalBlock;

typedef struct {
    int disk_id;
    bool online;
    PhysicalBlock blocks[MAX_BLOCKS_PER_DISK];
} PhysicalDisk;

PhysicalDisk raid_array[DISK_COUNT];
int next_stripe = 0;      /* próximo stripe livre */

void init_raid(void) {
    memset(raid_array, 0, sizeof(raid_array));
    for (int d = 0; d < DISK_COUNT; d++) {
        raid_array[d].disk_id = d + 1;
        raid_array[d].online = true;
    }
    next_stripe = 0;
}

static int parity_disk_of(int stripe) {
    return (DISK_COUNT - 1) - (stripe % DISK_COUNT);
}

/* Disco (0-based) do k-ésimo bloco de dados do stripe (pula o disco de paridade) */
static int data_disk_of(int stripe, int k) {
    int pd = parity_disk_of(stripe);
    return (k < pd) ? k : k + 1;
}

static int raid5_stripes_needed(int blocks) {
    int data_per_stripe = DISK_COUNT - 1;
    return (blocks + data_per_stripe - 1) / data_per_stripe;
}

/* XOR de todos os discos do stripe, exceto skip_disk.
 * Calcula a paridade (skip = disco de paridade) e reconstrói blocos (skip = disco falho). */
static void xor_stripe_except(int stripe, int skip_disk, unsigned char* out) {
    memset(out, 0, BLOCK_SIZE);
    for (int d = 0; d < DISK_COUNT; d++) {
        if (d == skip_disk) continue;
        const unsigned char* src = raid_array[d].blocks[stripe].content;
        for (int i = 0; i < BLOCK_SIZE; i++) {
            out[i] ^= src[i];
        }
    }
}

/* "/dados/planilha.csv" -> "Planilha" */
static void file_base_name(const char* path, char* out, size_t out_size) {
    const char* slash = strrchr(path, '/');
    const char* name = slash ? slash + 1 : path;
    size_t len = strcspn(name, ".");
    if (len == 0) {
        snprintf(out, out_size, "Arquivo");
        return;
    }
    if (len >= out_size) len = out_size - 1;
    memcpy(out, name, len);
    out[len] = '\0';
    out[0] = (char)toupper((unsigned char)out[0]);
}

/* Distribui no RAID os blocos de dados que o FS alocou para o arquivo. */
static void raid5_store_file(const char* filepath, int blocks_needed, const char* sample_data) {
    int data_per_stripe = DISK_COUNT - 1;
    int stripes_needed = raid5_stripes_needed(blocks_needed);

    printf("Arranjo Ativo: RAID 5 (%d Discos Físicos, Blocos de %d KB)\n\n",
           DISK_COUNT, BLOCK_SIZE / 1024);
    printf("[E/S - DISTRIBUIÇÃO EM DISCO]\n");

    char base[64];
    file_base_name(filepath, base, sizeof(base));

    for (int s = 0; s < stripes_needed; s++) {
        int stripe = next_stripe + s;
        int pd = parity_disk_of(stripe);
        char parity_label[128];
        size_t off = (size_t)snprintf(parity_label, sizeof(parity_label), "PARIDADE : XOR(");

        /* 1) Blocos de dados do stripe */
        for (int k = 0; k < data_per_stripe; k++) {
            int fb = s * data_per_stripe + k;          /* índice 0-based no arquivo */
            if (fb >= blocks_needed) break;            /* último stripe pode ficar incompleto */

            PhysicalBlock* pb = &raid_array[data_disk_of(stripe, k)].blocks[stripe];
            memset(pb->content, 0, BLOCK_SIZE);
            snprintf((char*)pb->content, BLOCK_SIZE, "Dados_Parte_%d: %s", fb + 1, sample_data);
            pb->occupied = true;
            pb->is_parity = false;
            pb->file_block = fb + 1;
            snprintf(pb->label, sizeof(pb->label), "Dados da %s - Part %d (%d KB)",
                     base, fb + 1, BLOCK_SIZE / 1024);

            off += (size_t)snprintf(parity_label + off, sizeof(parity_label) - off,
                                    "%sBloco %02d", (k == 0) ? "" : ", ", fb + 1);
        }
        snprintf(parity_label + off, sizeof(parity_label) - off, ")");

        /* 2) Paridade = XOR dos demais discos do stripe */
        PhysicalBlock* par = &raid_array[pd].blocks[stripe];
        xor_stripe_except(stripe, pd, par->content);
        par->occupied = true;
        par->is_parity = true;
        par->file_block = 0;
        snprintf(par->label, sizeof(par->label), "%s", parity_label);

        /* 3) Exibe a distribuição do stripe */
        if (stripes_needed > 1) {
            printf("Stripe %d:\n", stripe);
        }
        for (int d = 0; d < DISK_COUNT; d++) {
            PhysicalBlock* pb = &raid_array[d].blocks[stripe];
            if (!pb->occupied) {
                printf("Disco %d: [vazio]\n", d + 1);
            } else if (pb->is_parity) {
                printf("Disco %d: [%s]\n", d + 1, pb->label);
            } else {
                printf("Disco %d: [Bloco %02d: %s]\n", d + 1, pb->file_block, pb->label);
            }
        }
    }

    next_stripe += stripes_needed;
}

/* write_file --size: cria o arquivo no FS e grava seus blocos no RAID 5. */
void write_file_raid5(const char* filepath, int size_kb, const char* sample_data) {
    printf("> write_file %s --size %dKB\n", filepath, size_kb);

    if (size_kb <= 0) {
        printf("Erro: tamanho de arquivo inválido (%d KB).\n", size_kb);
        return;
    }

    /* Verifica o RAID antes de alocar no FS, para não deixar os dois inconsistentes */
    int blocks_needed = (int)(((size_t)size_kb * 1024 + BLOCK_SIZE - 1) / BLOCK_SIZE);
    if (next_stripe + raid5_stripes_needed(blocks_needed) > MAX_BLOCKS_PER_DISK) {
        printf("Erro: espaço insuficiente no arranjo RAID.\n");
        return;
    }

    FileNode* f = fs_create_file(filepath, size_kb, false);
    if (!f) return;

    raid5_store_file(f->full_path, f->num_data_blocks, sample_data);
}

void simulate_raid5_failure_and_reconstruction(int failed_disk_id) {
    if (failed_disk_id < 1 || failed_disk_id > DISK_COUNT) {
        printf("Erro: disco %d inexistente.\n", failed_disk_id);
        return;
    }

    int f = failed_disk_id - 1;
    static unsigned char backup[MAX_BLOCKS_PER_DISK][BLOCK_SIZE];

    printf("\n[TESTE DE FALHA SIMULADO]\n");
    printf("* Falha forçada no Disco %d!\n", failed_disk_id);

    /* Guarda uma cópia (só para conferir a reconstrução) e apaga o disco */
    for (int s = 0; s < next_stripe; s++) {
        memcpy(backup[s], raid_array[f].blocks[s].content, BLOCK_SIZE);
        memset(raid_array[f].blocks[s].content, 0, BLOCK_SIZE);
    }
    raid_array[f].online = false;

    /* RAID 5 tolera apenas 1 disco com falha */
    for (int d = 0; d < DISK_COUNT; d++) {
        if (d != f && !raid_array[d].online) {
            printf("* Mais de um disco offline: dados irrecuperáveis!\n");
            return;
        }
    }

    char survivors[64];
    survivors[0] = '\0';
    size_t off = 0;
    int shown = 0;
    for (int d = 0; d < DISK_COUNT; d++) {
        if (d == f) continue;
        off += (size_t)snprintf(survivors + off, sizeof(survivors) - off,
                                "%sDisco %d", (shown++ == 0) ? "" : " XOR ", d + 1);
    }

    /* Reconstrói cada stripe em uso: XOR de todos os discos sobreviventes */
    for (int s = 0; s < next_stripe; s++) {
        PhysicalBlock* pb = &raid_array[f].blocks[s];
        if (!pb->occupied) continue;

        unsigned char rebuilt[BLOCK_SIZE];
        xor_stripe_except(s, f, rebuilt);
        memcpy(pb->content, rebuilt, BLOCK_SIZE);

        bool ok = (memcmp(rebuilt, backup[s], BLOCK_SIZE) == 0);
        char what[48];
        if (pb->is_parity)         snprintf(what, sizeof(what), "Paridade (Stripe %d)", s);
        else if (next_stripe > 1)  snprintf(what, sizeof(what), "Bloco %02d (Stripe %d)", pb->file_block, s);
        else                       snprintf(what, sizeof(what), "Bloco %02d", pb->file_block);

        printf("* Recuperando %s via operação XOR: (%s) -> Reconstrução [%s]\n",
               what, survivors, ok ? "OK" : "FALHOU");
    }

    raid_array[f].online = true;
}

/* ============================================================================
 * MAIN — CENÁRIO COMPLETO (ETAPA 1 + EXEMPLOS 2.1 E 2.2)
 * ============================================================================ */

int main(void) {
    init_fs();
    init_raid();

    /* ---------- Etapa 1: preparação do sistema de arquivos ---------- */
    printf("=================== ETAPA 1 — SISTEMA DE ARQUIVOS ===================\n");
    mkdir_fs("/sistema");
    mkdir_fs("/sistema/logs");
    mkdir_fs("/dados");
    create_file_fs("/sistema/logs/app.log", 10);

    show_tree_recursive(root_node, "", 1);
    fs_status();

    /* ---------- Exemplo 2.1: write_file -> requisições de E/S -> SSTF ---------- */
    printf("\n=================== EXEMPLO 2.1 ===================\n");
    write_file_fs("/sistema/logs/app.log", "Novo Registro");

    /* ---------- Exemplo 2.2: write_file --size -> RAID 5 + falha ---------- */
    printf("\n=================== EXEMPLO 2.2 ===================\n");
    write_file_raid5("/dados/planilha.csv", 8, "Conteudo_Planilha_2026");
    simulate_raid5_failure_and_reconstruction(2);

    /* ---------- Estado final do FS (mostra planilha.csv alocada) ---------- */
    fs_status();

#ifdef EXTRA_TESTS
    printf("\n=================== TESTES EXTRAS ===================\n");
    read_file_fs("/sistema/logs/app.log");                 /* cabeça continua onde parou */

    printf("\n");
    write_file_fs("/nao/existe.txt", "x");                 /* erro: arquivo inexistente */
    create_file_fs("/dados/planilha.csv", 4);              /* erro: duplicado */

    printf("\n");
    write_file_raid5("/dados/relatorio.txt", 12, "Conteudo_Relatorio_2026");  /* 2 stripes */
    simulate_raid5_failure_and_reconstruction(1);
    simulate_raid5_failure_and_reconstruction(3);
    simulate_raid5_failure_and_reconstruction(2);

    printf("\n");
    write_file_raid5("/dados/grande.bin", 40, "X");         /* erro: sem espaço */
#endif

    free_tree(root_node);
    return 0;
}
