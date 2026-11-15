/*
 * TRABALHO INTEGRADO — Etapa 1 (Sistema de Arquivos) + Etapa 2 (E/S: SSTF e RAID 5)
 *                      + Etapa 3 (Segurança)
 *
 * Compilar : gcc -Wall -Wextra -o trabalho trabalho_etapa3_seguranca.c
 * Demo     : ./trabalho            (cenário completo, saída dos exemplos 2.1, 2.2, 3.1 e 3.2)
 * Shell    : ./trabalho -i         (interpretador de comandos interativo)
 * Extras   : gcc -Wall -Wextra -DEXTRA_TESTS -o trabalho trabalho_etapa3_seguranca.c
 *
 * Camadas (de cima para baixo):
 *
 *   Comandos (login, read_file, encrypt_file, antivirus_scan, ...)
 *        |
 *   SEGURANÇA : sessão (MODO_USUARIO / MODO_KERNEL), usuários e grupos (SHA-256 + salt),
 *               ACL rwx (dono/grupo/outros), auditoria, criptografia em repouso, integridade
 *        |
 *   SISTEMA DE ARQUIVOS (Etapa 1): árvore, i-nodes, blocos de dados com conteúdo
 *        |
 *   E/S (Etapa 2): blocos -> trilhas -> SSTF  |  RAID 5 com paridade rotativa
 *
 * Aviso: a criptografia (SHA-256 em modo contador) e o gerador de números pseudoaleatórios
 * são didáticos, feitos apenas para a simulação. Não use em sistemas reais.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <stdint.h>
#include <ctype.h>

#define BLOCK_SIZE           4096
#define TOTAL_BLOCKS         16     /* blocos do disco do sistema de arquivos */
#define MAX_CHILDREN         10
#define MAX_NAME             64
#define MAX_PATH             256

#define DISK_COUNT           3      /* discos físicos do RAID 5 */
#define MAX_BLOCKS_PER_DISK  16
#define MAX_REQUESTS         64

#define HASH_LEN             32
#define SALT_LEN             8
#define PW_ITERATIONS        1000   /* iterações do "key stretching" */
#define MAX_USERS            16
#define MAX_GROUPS           8
#define MAX_USER_GROUPS      4
#define MAX_LOG              128

/* Flags globais de apresentação */
static bool echo_cmd     = true;    /* imprime "> comando" (cenário roteirizado) */
static bool acl_trace    = false;   /* imprime também os acessos PERMITIDOS */
static bool io_verbose   = true;    /* imprime o escalonamento SSTF de cada operação */
static bool tree_show_acl = false;  /* mostra permissões na árvore */

/* Ponte entre os blocos lógicos do FS e os blocos físicos do RAID 5. */
static void raid_sync_block(int logical_block);
static void raid_unlink_block(int logical_block);

#define ECHO(...) do { if (echo_cmd) printf(__VA_ARGS__); } while (0)

/* ============================================================================
 * UTILIDADES
 * ============================================================================ */

static void safe_copy(char* dst, const char* src, size_t dst_size) {
    if (dst_size == 0) return;
    strncpy(dst, src, dst_size - 1);
    dst[dst_size - 1] = '\0';
}

static void to_hex(const uint8_t* in, size_t n, char* out, bool upper) {
    const char* digits = upper ? "0123456789ABCDEF" : "0123456789abcdef";
    for (size_t i = 0; i < n; i++) {
        out[2 * i]     = digits[in[i] >> 4];
        out[2 * i + 1] = digits[in[i] & 0x0F];
    }
    out[2 * n] = '\0';
}

static bool ct_equal(const uint8_t* a, const uint8_t* b, size_t n) {
    uint8_t diff = 0;
    for (size_t i = 0; i < n; i++) diff |= (uint8_t)(a[i] ^ b[i]);
    return diff == 0;
}

static bool find_bytes(const uint8_t* hay, size_t hlen, const char* needle) {
    size_t nlen = strlen(needle);
    if (nlen == 0 || hlen < nlen) return false;
    for (size_t i = 0; i + nlen <= hlen; i++) {
        if (hay[i] == (uint8_t)needle[0] && memcmp(hay + i, needle, nlen) == 0) return true;
    }
    return false;
}

/* ============================================================================
 * SHA-256 (implementação própria, validada no auto-teste do boot)
 * ============================================================================ */

typedef struct {
    uint8_t  data[64];
    uint32_t datalen;
    uint64_t bitlen;
    uint32_t state[8];
} Sha256Ctx;

static const uint32_t K256[64] = {
    0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
    0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
    0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
    0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
    0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
    0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
    0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
    0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2
};

#define ROTR(a, b) (((a) >> (b)) | ((a) << (32 - (b))))
#define CH(x, y, z)  (((x) & (y)) ^ (~(x) & (z)))
#define MAJ(x, y, z) (((x) & (y)) ^ ((x) & (z)) ^ ((y) & (z)))
#define EP0(x)  (ROTR(x, 2) ^ ROTR(x, 13) ^ ROTR(x, 22))
#define EP1(x)  (ROTR(x, 6) ^ ROTR(x, 11) ^ ROTR(x, 25))
#define SIG0(x) (ROTR(x, 7) ^ ROTR(x, 18) ^ ((x) >> 3))
#define SIG1(x) (ROTR(x, 17) ^ ROTR(x, 19) ^ ((x) >> 10))

static void sha256_transform(Sha256Ctx* ctx, const uint8_t data[]) {
    uint32_t a, b, c, d, e, f, g, h, i, j, t1, t2, m[64];

    for (i = 0, j = 0; i < 16; ++i, j += 4)
        m[i] = ((uint32_t)data[j] << 24) | ((uint32_t)data[j + 1] << 16) |
               ((uint32_t)data[j + 2] << 8) | ((uint32_t)data[j + 3]);
    for (; i < 64; ++i)
        m[i] = SIG1(m[i - 2]) + m[i - 7] + SIG0(m[i - 15]) + m[i - 16];

    a = ctx->state[0]; b = ctx->state[1]; c = ctx->state[2]; d = ctx->state[3];
    e = ctx->state[4]; f = ctx->state[5]; g = ctx->state[6]; h = ctx->state[7];

    for (i = 0; i < 64; ++i) {
        t1 = h + EP1(e) + CH(e, f, g) + K256[i] + m[i];
        t2 = EP0(a) + MAJ(a, b, c);
        h = g; g = f; f = e; e = d + t1;
        d = c; c = b; b = a; a = t1 + t2;
    }

    ctx->state[0] += a; ctx->state[1] += b; ctx->state[2] += c; ctx->state[3] += d;
    ctx->state[4] += e; ctx->state[5] += f; ctx->state[6] += g; ctx->state[7] += h;
}

static void sha256_init(Sha256Ctx* ctx) {
    ctx->datalen = 0;
    ctx->bitlen = 0;
    ctx->state[0] = 0x6a09e667; ctx->state[1] = 0xbb67ae85;
    ctx->state[2] = 0x3c6ef372; ctx->state[3] = 0xa54ff53a;
    ctx->state[4] = 0x510e527f; ctx->state[5] = 0x9b05688c;
    ctx->state[6] = 0x1f83d9ab; ctx->state[7] = 0x5be0cd19;
}

static void sha256_update(Sha256Ctx* ctx, const void* vdata, size_t len) {
    const uint8_t* data = (const uint8_t*)vdata;
    for (size_t i = 0; i < len; ++i) {
        ctx->data[ctx->datalen++] = data[i];
        if (ctx->datalen == 64) {
            sha256_transform(ctx, ctx->data);
            ctx->bitlen += 512;
            ctx->datalen = 0;
        }
    }
}

static void sha256_final(Sha256Ctx* ctx, uint8_t hash[HASH_LEN]) {
    uint32_t i = ctx->datalen;

    if (ctx->datalen < 56) {
        ctx->data[i++] = 0x80;
        while (i < 56) ctx->data[i++] = 0x00;
    } else {
        ctx->data[i++] = 0x80;
        while (i < 64) ctx->data[i++] = 0x00;
        sha256_transform(ctx, ctx->data);
        memset(ctx->data, 0, 56);
    }

    ctx->bitlen += (uint64_t)ctx->datalen * 8;
    for (int k = 0; k < 8; k++) {
        ctx->data[63 - k] = (uint8_t)(ctx->bitlen >> (8 * k));
    }
    sha256_transform(ctx, ctx->data);

    for (i = 0; i < 4; ++i) {
        for (uint32_t j = 0; j < 8; ++j) {
            hash[i + j * 4] = (uint8_t)((ctx->state[j] >> (24 - i * 8)) & 0xff);
        }
    }
}

static void sha256_buf(const void* data, size_t len, uint8_t out[HASH_LEN]) {
    Sha256Ctx c;
    sha256_init(&c);
    sha256_update(&c, data, len);
    sha256_final(&c, out);
}

static bool sha256_selftest(void) {
    static const uint8_t expected[HASH_LEN] = {
        0xba,0x78,0x16,0xbf,0x8f,0x01,0xcf,0xea,0x41,0x41,0x40,0xde,0x5d,0xae,0x22,0x23,
        0xb0,0x03,0x61,0xa3,0x96,0x17,0x7a,0x9c,0xb4,0x10,0xff,0x61,0xf2,0x00,0x15,0xad
    };
    uint8_t h[HASH_LEN];
    sha256_buf("abc", 3, h);
    return memcmp(h, expected, HASH_LEN) == 0;
}

/* Derivação de chave/hash de senha: SHA-256 com salt, repetido PW_ITERATIONS vezes
 * (dificulta ataques de força bruta e de dicionário). */
static void kdf_sha256(const uint8_t salt[SALT_LEN], const char* secret, uint8_t out[HASH_LEN]) {
    Sha256Ctx c;
    sha256_init(&c);
    sha256_update(&c, salt, SALT_LEN);
    sha256_update(&c, secret, strlen(secret));
    sha256_final(&c, out);
    for (int i = 1; i < PW_ITERATIONS; i++) {
        sha256_init(&c);
        sha256_update(&c, out, HASH_LEN);
        sha256_update(&c, salt, SALT_LEN);
        sha256_update(&c, secret, strlen(secret));
        sha256_final(&c, out);
    }
}

/* Gerador pseudoaleatório determinístico (xorshift64): didático e reproduzível. */
static uint64_t rng_state = 0x2026A5C0FFEE1234ULL;
static void rng_bytes(uint8_t* out, size_t n) {
    for (size_t i = 0; i < n; i++) {
        rng_state ^= rng_state << 13;
        rng_state ^= rng_state >> 7;
        rng_state ^= rng_state << 17;
        out[i] = (uint8_t)(rng_state >> 24);
    }
}

/* ============================================================================
 * TIPOS
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
    uint8_t data[BLOCK_SIZE];        /* conteúdo físico do bloco */
    uint8_t hash[HASH_LEN];          /* "registro oficial" SHA-256 do bloco */
    bool hash_valid;
} DiskBlock;

typedef struct FileNode {
    char name[MAX_NAME];
    int is_dir;
    size_t size;                     /* tamanho declarado, em bytes */
    int inode_block;
    int data_blocks[TOTAL_BLOCKS];
    int num_data_blocks;
    char full_path[MAX_PATH];

    /* Etapa 3: controle de acesso e proteção de dados */
    int uid, gid;                    /* proprietário e grupo */
    int mode;                        /* bits rwxrwxrwx (ex.: 0750) */
    size_t content_len;              /* bytes realmente gravados */
    bool encrypted;
    uint8_t enc_nonce[SALT_LEN];
    uint8_t key_check[HASH_LEN];     /* verificador da chave (não revela a chave) */

    struct FileNode* parent;
    struct FileNode* children[MAX_CHILDREN];
    int child_count;
} FileNode;

typedef struct { char name[32]; int gid; } Group;

typedef struct {
    char name[32];
    int uid;
    int gid;                         /* grupo primário */
    int extra_groups[MAX_USER_GROUPS];
    int extra_count;
    uint8_t salt[SALT_LEN];
    uint8_t pw_hash[HASH_LEN];       /* a senha em texto nunca é armazenada */
} User;

typedef struct {
    int seq;
    char who[32];
    char action[28];
    char object[MAX_PATH];
    char result[12];
} LogEntry;

/* ============================================================================
 * ESTADO GLOBAL
 * ============================================================================ */

static DiskBlock disk[TOTAL_BLOCKS];
static int free_blocks_count = TOTAL_BLOCKS;
static int root_block = -1;
static FileNode* root_node = NULL;
static FileNode* file_registry[TOTAL_BLOCKS];
static int registry_count = 0;

static Group groups[MAX_GROUPS];
static int group_count = 0;
static User users[MAX_USERS];
static int user_count = 0;
static int next_uid = 1000;
static const User* session_user = NULL;

static LogEntry audit_log[MAX_LOG];
static int log_count = 0;
static int log_seq = 0;

/* ============================================================================
 * ETAPA 3.A — AUDITORIA
 * ============================================================================ */

static void audit_as(const char* who, const char* action, const char* object, const char* result) {
    if (log_count == MAX_LOG) {
        memmove(&audit_log[0], &audit_log[1], sizeof(LogEntry) * (MAX_LOG - 1));
        log_count--;
    }
    LogEntry* e = &audit_log[log_count++];
    e->seq = ++log_seq;
    safe_copy(e->who, who, sizeof(e->who));
    safe_copy(e->action, action, sizeof(e->action));
    safe_copy(e->object, object, sizeof(e->object));
    safe_copy(e->result, result, sizeof(e->result));
}

static void audit(const char* action, const char* object, const char* result) {
    audit_as(session_user ? session_user->name : "(sem sessão)", action, object, result);
}

/* ============================================================================
 * ETAPA 3.B — IDENTIDADE: USUÁRIOS, GRUPOS E SESSÃO
 * ============================================================================ */

static int find_group(const char* name) {
    for (int i = 0; i < group_count; i++)
        if (strcmp(groups[i].name, name) == 0) return groups[i].gid;
    return -1;
}

static const char* group_name(int gid) {
    for (int i = 0; i < group_count; i++)
        if (groups[i].gid == gid) return groups[i].name;
    return "?";
}

static User* find_user(const char* name) {
    for (int i = 0; i < user_count; i++)
        if (strcmp(users[i].name, name) == 0) return &users[i];
    return NULL;
}

static const char* user_name(int uid) {
    for (int i = 0; i < user_count; i++)
        if (users[i].uid == uid) return users[i].name;
    return "?";
}

static bool user_in_group(const User* u, int gid) {
    if (u->gid == gid) return true;
    for (int i = 0; i < u->extra_count; i++)
        if (u->extra_groups[i] == gid) return true;
    return false;
}

static bool valid_name(const char* s) {
    size_t len = strlen(s);
    if (len == 0 || len >= 32) return false;
    for (size_t i = 0; i < len; i++) {
        if (!isalnum((unsigned char)s[i]) && s[i] != '_' && s[i] != '-') return false;
    }
    return true;
}

static bool is_kernel(void) { return session_user && session_user->uid == 0; }
static const char* mode_name(void) { return is_kernel() ? "MODO_KERNEL" : "MODO_USUARIO"; }

static int group_create(const char* name) {
    int gid = group_count;
    groups[group_count].gid = gid;
    safe_copy(groups[group_count].name, name, sizeof(groups[group_count].name));
    group_count++;
    return gid;
}

static User* user_create(const char* name, const char* password, int gid, int uid) {
    User* u = &users[user_count++];
    memset(u, 0, sizeof(*u));
    safe_copy(u->name, name, sizeof(u->name));
    u->uid = uid;
    u->gid = gid;
    rng_bytes(u->salt, SALT_LEN);
    kdf_sha256(u->salt, password, u->pw_hash);
    return u;
}

static bool require_session(void) {
    if (!session_user) {
        printf("Erro: nenhuma sessão ativa. Use 'login --user <nome>'.\n");
        return false;
    }
    return true;
}

/* Operações críticas só podem ser executadas em MODO_KERNEL (root). */
static bool require_kernel(const char* op) {
    if (!require_session()) return false;
    if (is_kernel()) return true;
    printf("[NEGADO]: A operação '%s' é crítica e exige MODO_KERNEL (usuário atual: '%s' | Modo: MODO_USUARIO).\n"
           "Tentativa não autorizada registrada nos logs do sistema.\n", op, session_user->name);
    char up[28];
    size_t i = 0;
    for (; op[i] && i < sizeof(up) - 1; i++) up[i] = (char)toupper((unsigned char)op[i]);
    up[i] = '\0';
    audit(up, "(operacao critica)", "NEGADO");
    return false;
}

static void security_boot(void) {
    printf("=================== BOOT DO SIMULADOR ===================\n");
    if (!sha256_selftest()) {
        printf("[BOOT] FALHA no auto-teste do SHA-256. Abortando.\n");
        exit(1);
    }
    printf("[BOOT] Auto-teste SHA-256: OK\n");
    int admin = group_create("admin");
    user_create("root", "Root@2026", admin, 0);
    printf("[BOOT] Kernel iniciado | Grupo padrão: 'admin' | Superusuário: 'root' (uid=0)\n\n");
}

void cmd_login(const char* name, const char* password) {
    if (echo_cmd) {
        printf("> login --user %s\nSenha: ", name);
        for (size_t i = 0; i < strlen(password); i++) putchar('*');
        putchar('\n');
    }

    User* u = find_user(name);
    uint8_t salt_dummy[SALT_LEN] = {0};
    uint8_t h[HASH_LEN];
    kdf_sha256(u ? u->salt : salt_dummy, password, h);   /* mesmo custo para usuário inexistente */

    if (!u || !ct_equal(h, u->pw_hash, HASH_LEN)) {
        session_user = NULL; /* autenticação malsucedida não mantém privilégios anteriores */
        printf("Falha de autenticação: usuário ou senha inválidos.\n");
        audit_as(name, "LOGIN", "(autenticacao)", "FALHA");
        return;
    }

    session_user = u;
    printf("Autenticado com sucesso. Usuário: '%s' | Grupo: '%s' | Modo: %s\n",
           u->name, group_name(u->gid), mode_name());
    audit("LOGIN", "(autenticacao)", "OK");
}

void cmd_logout(void) {
    ECHO("> logout\n");
    if (!session_user) {
        printf("Nenhuma sessão ativa.\n");
        return;
    }
    printf("Sessão de '%s' encerrada.\n", session_user->name);
    audit("LOGOUT", "(sessao)", "OK");
    session_user = NULL;
}

void cmd_whoami(void) {
    ECHO("> whoami\n");
    if (!session_user) {
        printf("Nenhuma sessão ativa.\n");
        return;
    }
    printf("Usuário: '%s' (uid=%d) | Grupo: '%s' | Modo: %s\n",
           session_user->name, session_user->uid, group_name(session_user->gid), mode_name());
}

void cmd_groupadd(const char* name) {
    ECHO("> groupadd %s\n", name);
    if (!require_kernel("groupadd")) return;
    if (!valid_name(name)) { printf("Erro: nome de grupo inválido.\n"); return; }
    if (find_group(name) >= 0) { printf("Erro: o grupo '%s' já existe.\n", name); return; }
    if (group_count >= MAX_GROUPS) { printf("Erro: limite de grupos atingido.\n"); return; }
    int gid = group_create(name);
    printf("Grupo '%s' criado (gid=%d).\n", name, gid);
    audit("GROUPADD", name, "OK");
}

void cmd_useradd(const char* name, const char* group, const char* password) {
    ECHO("> useradd %s --group %s\n", name, group);
    if (!require_kernel("useradd")) return;
    if (!valid_name(name)) { printf("Erro: nome de usuário inválido.\n"); return; }
    if (find_user(name)) { printf("Erro: o usuário '%s' já existe.\n", name); return; }
    int gid = find_group(group);
    if (gid < 0) { printf("Erro: grupo '%s' inexistente.\n", group); return; }
    if (strlen(password) < 8) { printf("Erro: a senha deve ter ao menos 8 caracteres.\n"); return; }
    if (user_count >= MAX_USERS) { printf("Erro: limite de usuários atingido.\n"); return; }

    User* u = user_create(name, password, gid, next_uid++);
    printf("Usuário '%s' cadastrado (uid=%d, grupo primário '%s').\n", u->name, u->uid, group_name(gid));
    printf("Senha guardada como SHA-256 com salt de %d bytes e %d iterações (texto puro nunca é armazenado).\n",
           SALT_LEN, PW_ITERATIONS);
    audit("USERADD", name, "OK");
}

void cmd_usermod_add_group(const char* name, const char* group) {
    ECHO("> usermod %s --add-group %s\n", name, group);
    if (!require_kernel("usermod")) return;
    User* u = find_user(name);
    int gid = find_group(group);
    if (!u) { printf("Erro: usuário '%s' inexistente.\n", name); return; }
    if (gid < 0) { printf("Erro: grupo '%s' inexistente.\n", group); return; }
    if (user_in_group(u, gid)) { printf("'%s' já pertence ao grupo '%s'.\n", name, group); return; }
    if (u->extra_count >= MAX_USER_GROUPS) { printf("Erro: limite de grupos por usuário atingido.\n"); return; }
    u->extra_groups[u->extra_count++] = gid;
    printf("Usuário '%s' adicionado ao grupo '%s'.\n", name, group);
    audit("USERMOD", name, "OK");
}

void cmd_show_users(void) {
    ECHO("> show_users\n");
    if (!require_kernel("show_users")) return;
    printf("[CADASTRO DE USUÁRIOS E GRUPOS]\nGrupos:");
    for (int i = 0; i < group_count; i++) printf(" %s(gid=%d)", groups[i].name, groups[i].gid);
    printf("\n");
    for (int i = 0; i < user_count; i++) {
        const User* u = &users[i];
        char salt_hex[2 * SALT_LEN + 1], hash_hex[2 * HASH_LEN + 1];
        to_hex(u->salt, SALT_LEN, salt_hex, false);
        to_hex(u->pw_hash, HASH_LEN, hash_hex, false);
        hash_hex[32] = '\0';
        printf("uid=%-5d %-8s grupo=%-6s", u->uid, u->name, group_name(u->gid));
        for (int g = 0; g < u->extra_count; g++) printf(" +%s", group_name(u->extra_groups[g]));
        printf("\n           salt=%s sha256=%s...\n", salt_hex, hash_hex);
    }
}

void cmd_show_logs(void) {
    ECHO("> show_logs\n");
    if (!require_kernel("show_logs")) return;
    printf("[LOG DE AUDITORIA DO SISTEMA] (%d registros)\n", log_count);
    for (int i = 0; i < log_count; i++) {
        const LogEntry* e = &audit_log[i];
        printf("#%03d %-8s %-14s %-32s %s\n", e->seq, e->who, e->action, e->object, e->result);
    }
}

/* ============================================================================
 * ETAPA 3.C — CONTROLE DE ACESSO (PERMISSÕES rwx PARA DONO / GRUPO / OUTROS)
 * ============================================================================ */

static void node_path(const FileNode* n, char* out, size_t sz) {
    if (!n->parent) {
        snprintf(out, sz, "/");
        return;
    }
    char parent[MAX_PATH];
    node_path(n->parent, parent, sizeof(parent));
    snprintf(out, sz, "%s%s%s", parent, strcmp(parent, "/") == 0 ? "" : "/", n->name);
}

static void mode_to_string(int mode, char out[10]) {
    const char* rwx = "rwxrwxrwx";
    for (int i = 0; i < 9; i++) out[i] = (mode & (1 << (8 - i))) ? rwx[i] : '-';
    out[9] = '\0';
}

static int perm_bit(char perm) { return perm == 'r' ? 4 : (perm == 'w' ? 2 : 1); }

static const char* perm_word(char perm) {
    return perm == 'r' ? "leitura" : (perm == 'w' ? "escrita" : "execução");
}

/* Bits (0..7) aplicáveis ao usuário: classe dono, grupo ou outros. */
static int class_bits(const User* u, const FileNode* n) {
    if (u->uid == 0) return 7;
    if (u->uid == n->uid) return (n->mode >> 6) & 7;
    if (user_in_group(u, n->gid)) return (n->mode >> 3) & 7;
    return n->mode & 7;
}

static bool check_access(const FileNode* n, char perm, const char* action, bool trace_ok) {
    if (!require_session()) return false;

    char path[MAX_PATH], modestr[10];
    node_path(n, path, sizeof(path));
    mode_to_string(n->mode, modestr);

    bool allowed = is_kernel() || (class_bits(session_user, n) & perm_bit(perm));
    if (allowed) {
        if (trace_ok && acl_trace) {
            printf("[ACL] %s em '%s' por '%s': PERMITIDO (%s%s)\n", action, path,
                   session_user->name, modestr, is_kernel() ? ", MODO_KERNEL" : "");
        }
        return true;
    }

    printf("[SISTEMA DE SEGURANÇA - VERIFICAÇÃO DE ACL]\n");
    printf("Objeto      : %s\n", path);
    printf("Proprietário: %s (Grupo: %s)\n", user_name(n->uid), group_name(n->gid));
    printf("Permissões  : %s (%03o)\n", modestr, (unsigned)n->mode);
    printf("Ação Pedida : %s por '%s' (Grupo: %s)\n\n", action, session_user->name,
           group_name(session_user->gid));
    printf("[NEGADO]: O usuário '%s' não possui permissão de %s no objeto '%s'.\n",
           session_user->name, perm_word(perm), path);
    printf("Tentativa não autorizada registrada nos logs do sistema.\n");
    audit(action, path, "NEGADO");
    return false;
}

/* Para alcançar um objeto é preciso ter 'x' em todos os diretórios do caminho. */
static bool check_ancestors(const FileNode* n) {
    const FileNode* chain[32];
    int depth = 0;
    for (const FileNode* p = n->parent; p && depth < 32; p = p->parent) chain[depth++] = p;
    for (int i = depth - 1; i >= 0; i--) {
        if (!check_access(chain[i], 'x', "TRAVESSIA", false)) return false;
    }
    return true;
}

static bool check_path_access(const FileNode* n, char perm, const char* action) {
    if (!require_session()) return false;
    if (!check_ancestors(n)) return false;
    return check_access(n, perm, action, true);
}

/* ============================================================================
 * ETAPA 1 — SISTEMA DE ARQUIVOS (agora com conteúdo, dono e permissões)
 * ============================================================================ */

static void fs_record_hash(int blk) {
    sha256_buf(disk[blk].data, BLOCK_SIZE, disk[blk].hash);
    disk[blk].hash_valid = true;
}

int allocate_block(const char* desc, BlockType type) {
    for (int i = 0; i < TOTAL_BLOCKS; i++) {
        if (disk[i].type == BLOCK_FREE) {
            disk[i].type = type;
            safe_copy(disk[i].description, desc, sizeof(disk[i].description));
            memset(disk[i].data, 0, BLOCK_SIZE);
            disk[i].hash_valid = false;
            if (type == BLOCK_DATA) fs_record_hash(i);
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
        disk[index].hash_valid = false;
        memset(disk[index].data, 0, BLOCK_SIZE);
        free_blocks_count++;
    }
}

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
    node->uid = session_user ? session_user->uid : 0;
    node->gid = session_user ? session_user->gid : 0;
    node->mode = is_dir ? 0755 : 0644;
    return node;
}

void free_tree(FileNode* node) {
    if (!node) return;
    for (int i = 0; i < node->child_count; i++) free_tree(node->children[i]);
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

/* ---------- Conteúdo dos arquivos nos blocos físicos ---------- */

/* Grava 'len' bytes nos blocos de dados do arquivo e atualiza o registro oficial de hash. */
static bool fs_store_bytes(FileNode* f, const uint8_t* buf, size_t len) {
    if (len > (size_t)f->num_data_blocks * BLOCK_SIZE) return false;
    size_t off = 0;
    for (int i = 0; i < f->num_data_blocks; i++) {
        int blk = f->data_blocks[i];
        memset(disk[blk].data, 0, BLOCK_SIZE);
        if (off < len) {
            size_t chunk = (len - off > BLOCK_SIZE) ? BLOCK_SIZE : (len - off);
            memcpy(disk[blk].data, buf + off, chunk);
            off += chunk;
        }
        fs_record_hash(blk);
        raid_sync_block(blk);
    }
    f->content_len = len;
    return true;
}

static void fs_load_bytes(const FileNode* f, uint8_t* buf, size_t len) {
    size_t off = 0;
    for (int i = 0; i < f->num_data_blocks && off < len; i++) {
        size_t chunk = (len - off > BLOCK_SIZE) ? BLOCK_SIZE : (len - off);
        memcpy(buf + off, disk[f->data_blocks[i]].data, chunk);
        off += chunk;
    }
}

/* ---------- Operações do FS ---------- */

void mkdir_fs(const char* path) {
    if (!require_session()) return;

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

    if (!check_path_access(parent, 'w', "CRIAÇÃO DE DIRETÓRIO") ||
        !check_access(parent, 'x', "TRAVESSIA", true)) return;

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
    if (echo_cmd) printf("> mkdir %s\n", path);
    else          printf("Diretório '%s' criado.\n", path);
}

/* Cria o arquivo no FS (i-node + blocos de dados). Retorna o nó ou NULL. */
FileNode* fs_create_file(const char* path, int size_kb, bool echo) {
    if (!require_session()) return NULL;

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

    if (!check_path_access(parent, 'w', "CRIAÇÃO DE ARQUIVO") ||
        !check_access(parent, 'x', "TRAVESSIA", true)) return NULL;

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
    FileNode* f = fs_create_file(path, size_kb, echo_cmd);
    if (f && !echo_cmd) printf("Arquivo '%s' criado (%d KB).\n", path, size_kb);
}

/* Operações recuperadas da Etapa 1, com controle de acesso. */
void delete_fs(const char* path) {
    if (!require_session()) return;
    FileNode* n = traverse_path(path);
    if (!n || n == root_node) { printf("Erro: objeto inexistente ou raiz protegida.\n"); return; }
    FileNode* parent = n->parent;
    if (!check_path_access(parent, 'w', "EXCLUSÃO") ||
        !check_access(parent, 'x', "TRAVESSIA", true)) return;
    if (n->is_dir && n->child_count) {
        printf("Erro: diretório não está vazio.\n"); return;
    }
    if (!n->is_dir) {
        for (int i = 0; i < n->num_data_blocks; i++) {
            raid_unlink_block(n->data_blocks[i]);
            free_block(n->data_blocks[i]);
        }
        free_block(n->inode_block);
        for (int i = 0; i < registry_count; i++) {
            if (file_registry[i] == n) {
                memmove(&file_registry[i], &file_registry[i + 1],
                        (size_t)(registry_count - i - 1) * sizeof(file_registry[0]));
                registry_count--;
                break;
            }
        }
    }
    for (int i = 0; i < parent->child_count; i++) {
        if (parent->children[i] == n) {
            memmove(&parent->children[i], &parent->children[i + 1],
                    (size_t)(parent->child_count - i - 1) * sizeof(parent->children[0]));
            parent->child_count--;
            break;
        }
    }
    audit("DELETE", path, "OK");
    free(n);
    printf("Objeto '%s' excluído.\n", path);
}

void update_file_fs(const char* path, int new_size_kb) {
    if (!require_session()) return;
    FileNode* f = traverse_path(path);
    if (!f || f->is_dir) { printf("Erro: arquivo inexistente.\n"); return; }
    if (!check_path_access(f, 'w', "ESCRITA")) return;
    if (f->encrypted) { printf("Erro: descriptografe o arquivo antes de redimensioná-lo.\n"); return; }
    if (new_size_kb <= 0 || new_size_kb > TOTAL_BLOCKS * (BLOCK_SIZE / 1024)) {
        printf("Erro: tamanho inválido.\n"); return;
    }
    size_t new_size = (size_t)new_size_kb * 1024;
    int target = (int)((new_size + BLOCK_SIZE - 1) / BLOCK_SIZE);
    if (target > f->num_data_blocks + free_blocks_count) {
        printf("Erro: espaço em disco insuficiente.\n"); return;
    }
    while (f->num_data_blocks > target) {
        int blk = f->data_blocks[--f->num_data_blocks];
        raid_unlink_block(blk);
        free_block(blk);
    }
    while (f->num_data_blocks < target) {
        char desc[128];
        snprintf(desc, sizeof(desc), "'%s' (bloco adicional)", path);
        int blk = allocate_block(desc, BLOCK_DATA);
        if (blk < 0) { printf("Erro: falha ao alocar bloco.\n"); return; }
        f->data_blocks[f->num_data_blocks++] = blk;
    }
    f->size = new_size;
    if (f->content_len > new_size) f->content_len = new_size;
    audit("RESIZE", path, "OK");
    printf("Arquivo '%s' redimensionado para %d KB.\n", path, new_size_kb);
}

/* ---------- Exibição e relatório ---------- */

static void print_acl_suffix(const FileNode* n) {
    if (!tree_show_acl) return;
    char modestr[10];
    mode_to_string(n->mode, modestr);
    printf("  %s %s:%s", modestr, user_name(n->uid), group_name(n->gid));
}

void show_tree_recursive(FileNode* node, const char* prefix, int is_root) {
    if (!node || !require_session()) return;
    if (!is_kernel() && !check_path_access(node, 'r', "LISTAGEM")) return;
    if (is_root) {
        printf("\n[ÁRVORE DO SISTEMA DE ARQUIVOS]\n/");
        print_acl_suffix(node);
        printf("\n");
    }

    for (int i = 0; i < node->child_count; i++) {
        FileNode* child = node->children[i];
        int is_last = (i == node->child_count - 1);
        const char* connector = is_last ? "└── " : "├── ";

        if (child->is_dir) {
            printf("%s%s%s/ [DIR]", prefix, connector, child->name);
            print_acl_suffix(child);
            printf("\n");
            char new_prefix[256];
            snprintf(new_prefix, sizeof(new_prefix), "%s%s", prefix, is_last ? "    " : "│   ");
            show_tree_recursive(child, new_prefix, 0);
        } else {
            printf("%s%s%s (%zu KB) [ARQ]", prefix, connector, child->name, child->size / 1024);
            print_acl_suffix(child);
            printf("\n");
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
    if (!require_kernel("fs_status")) return;
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
    memset(disk, 0, sizeof(disk));
    for (int i = 0; i < TOTAL_BLOCKS; i++) disk[i].type = BLOCK_FREE;
    free_blocks_count = TOTAL_BLOCKS;
    registry_count = 0;
    root_node = create_node("/", 1, NULL);
    root_block = allocate_block("Diretório '/'", BLOCK_INODE_ROOT);
    root_node->inode_block = root_block;
}

/* ============================================================================
 * ETAPA 2.1 — INTEGRAÇÃO FS -> E/S E ESCALONAMENTO DO BRAÇO (SSTF)
 * ============================================================================ */

/* Em qual trilha física cada bloco do FS está gravado. */
static const int block_to_track[TOTAL_BLOCKS] = {
     98, 183,  37, 122,  14,  65,  67, 124,
     21,  80, 150,   9,  45, 170, 110,  30
};

static int disk_head = 53;   /* posição atual da cabeça (persiste entre operações) */

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
int simulate_sstf_scheduling(int initial_head, const int requests[], int num_requests, bool verbose) {
    if (num_requests <= 0 || num_requests > MAX_REQUESTS) {
        if (verbose) printf("Erro: número de requisições inválido (%d).\n", num_requests);
        return initial_head;
    }

    bool visited[MAX_REQUESTS] = { false };
    int order[MAX_REQUESTS + 1];
    int moves[MAX_REQUESTS];
    int current_pos = initial_head;
    int total_movement = 0;

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

    if (verbose) {
        printf("[E/S] Requisições de leitura/escrita pendentes nas trilhas: [");
        for (int i = 0; i < num_requests; i++) {
            printf("%d%s", requests[i], (i == num_requests - 1) ? "" : ", ");
        }
        printf("]\nPosição atual da cabeça de leitura: Trilha %d\n\n", initial_head);
        printf("--- ESCALONAMENTO DE DISCO: SSTF (Shortest Seek Time First) ---\n");

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
    }

    return current_pos;
}

/* Envia a lista de blocos tocados por uma operação do FS ao disco. */
static void io_submit(const int blocks[], int n) {
    int tracks[MAX_REQUESTS];
    int count = blocks_to_tracks(blocks, n, tracks);
    disk_head = simulate_sstf_scheduling(disk_head, tracks, count, io_verbose);
}

/* Blocos tocados por uma operação sobre o arquivo (i-node + dados, opcionalmente o diretório). */
static void io_submit_file(const FileNode* f, bool touch_root) {
    int blocks[TOTAL_BLOCKS + 2];
    int n = 0;
    if (touch_root) blocks[n++] = root_block;
    blocks[n++] = f->inode_block;
    for (int i = 0; i < f->num_data_blocks; i++) blocks[n++] = f->data_blocks[i];
    io_submit(blocks, n);
}

/* ============================================================================
 * ETAPA 3.D — CRIPTOGRAFIA EM REPOUSO
 * ============================================================================
 * Chave do usuário -> KDF (SHA-256 + salt aleatório do arquivo, 1000 iterações).
 * Cifra: fluxo de bytes gerado por SHA-256(chave || nonce || contador), combinado por XOR
 * com o texto. O conteúdo é cifrado ANTES de ir para o bloco físico.
 */

static void derive_file_key(const FileNode* f, const char* key, uint8_t dk[HASH_LEN]) {
    kdf_sha256(f->enc_nonce, key, dk);
}

static void key_check_of(const uint8_t dk[HASH_LEN], uint8_t out[HASH_LEN]) {
    Sha256Ctx c;
    sha256_init(&c);
    sha256_update(&c, "KEYCHECK", 8);
    sha256_update(&c, dk, HASH_LEN);
    sha256_final(&c, out);
}

static void keystream_xor(const uint8_t dk[HASH_LEN], const uint8_t nonce[SALT_LEN],
                          uint8_t* buf, size_t len) {
    uint32_t counter = 0;
    for (size_t off = 0; off < len; off += HASH_LEN, counter++) {
        uint8_t in[HASH_LEN + SALT_LEN + 4], ks[HASH_LEN];
        memcpy(in, dk, HASH_LEN);
        memcpy(in + HASH_LEN, nonce, SALT_LEN);
        in[HASH_LEN + SALT_LEN]     = (uint8_t)(counter >> 24);
        in[HASH_LEN + SALT_LEN + 1] = (uint8_t)(counter >> 16);
        in[HASH_LEN + SALT_LEN + 2] = (uint8_t)(counter >> 8);
        in[HASH_LEN + SALT_LEN + 3] = (uint8_t)counter;
        sha256_buf(in, sizeof(in), ks);
        for (size_t j = 0; j < HASH_LEN && off + j < len; j++) buf[off + j] ^= ks[j];
    }
}

static bool key_matches(const FileNode* f, const char* key) {
    uint8_t dk[HASH_LEN], chk[HASH_LEN];
    derive_file_key(f, key, dk);
    key_check_of(dk, chk);
    return ct_equal(chk, f->key_check, HASH_LEN);
}

static void print_cipher_hex(const FileNode* f) {
    size_t n = f->content_len < 8 ? f->content_len : 8;
    printf("\"0x");
    for (size_t i = 0; i < n; i++) printf("%02X", disk[f->data_blocks[0]].data[i]);
    printf("... (Encrypted Ciphertext)\"");
}

void cmd_encrypt_file(const char* path, const char* key) {
    ECHO("> encrypt_file %s --key ********\n", path);
    if (!require_session()) return;

    FileNode* f = traverse_path(path);
    if (!f || f->is_dir) { printf("Erro: arquivo '%s' inexistente.\n", path); return; }
    if (!check_path_access(f, 'r', "LEITURA") || !check_access(f, 'w', "ESCRITA", true)) return;

    if (f->encrypted) { printf("Erro: '%s' já está criptografado.\n", path); return; }
    if (key[0] == '\0') { printf("Erro: chave vazia.\n"); return; }
    if (f->content_len == 0) { printf("Erro: o arquivo está vazio; nada a criptografar.\n"); return; }

    size_t len = f->content_len;
    uint8_t* buf = (uint8_t*)malloc(len);
    if (!buf) { printf("Erro: sem memória.\n"); return; }
    fs_load_bytes(f, buf, len);

    rng_bytes(f->enc_nonce, SALT_LEN);
    uint8_t dk[HASH_LEN];
    derive_file_key(f, key, dk);
    key_check_of(dk, f->key_check);
    keystream_xor(dk, f->enc_nonce, buf, len);

    fs_store_bytes(f, buf, len);      /* o bloco físico recebe apenas o texto cifrado */
    free(buf);
    f->encrypted = true;

    io_submit_file(f, false);
    audit("ENCRYPT", path, "OK");

    printf("Arquivo '%s' criptografado com sucesso.\n", path);
    printf("Conteúdo gravado nos blocos físicos: ");
    print_cipher_hex(f);
    printf("\n");
}

void cmd_decrypt_file(const char* path, const char* key) {
    ECHO("> decrypt_file %s --key ********\n", path);
    if (!require_session()) return;

    FileNode* f = traverse_path(path);
    if (!f || f->is_dir) { printf("Erro: arquivo '%s' inexistente.\n", path); return; }
    if (!check_path_access(f, 'r', "LEITURA") || !check_access(f, 'w', "ESCRITA", true)) return;
    if (!f->encrypted) { printf("Erro: '%s' não está criptografado.\n", path); return; }

    if (!key_matches(f, key)) {
        printf("[NEGADO]: Chave incorreta para '%s'. Tentativa registrada nos logs do sistema.\n", path);
        audit("DECRYPT", path, "NEGADO");
        return;
    }

    size_t len = f->content_len;
    uint8_t* buf = (uint8_t*)malloc(len);
    if (!buf) { printf("Erro: sem memória.\n"); return; }
    fs_load_bytes(f, buf, len);
    uint8_t dk[HASH_LEN];
    derive_file_key(f, key, dk);
    keystream_xor(dk, f->enc_nonce, buf, len);
    fs_store_bytes(f, buf, len);
    free(buf);
    f->encrypted = false;

    io_submit_file(f, false);
    audit("DECRYPT", path, "OK");
    printf("Arquivo '%s' descriptografado com sucesso.\n", path);
}

/* ============================================================================
 * ETAPA 3.E — INTEGRIDADE: HASH DOS BLOCOS E ANTIVÍRUS SIMULADO
 * ============================================================================ */

static const char* MALWARE_SIGNATURES[] = {
    "MALWARE_SIG_X1",
    "ransomware_payload",
    "EICAR-SIM-TEST"
};
#define NUM_SIGNATURES ((int)(sizeof(MALWARE_SIGNATURES) / sizeof(MALWARE_SIGNATURES[0])))

/* Compara o hash atual de cada bloco de dados com o "registro oficial". */
static bool file_hash_check(const FileNode* f, char* bad_list, size_t sz) {
    bool ok = true;
    size_t used = 0;
    bad_list[0] = '\0';
    for (int i = 0; i < f->num_data_blocks; i++) {
        int b = f->data_blocks[i];
        uint8_t h[HASH_LEN];
        sha256_buf(disk[b].data, BLOCK_SIZE, h);
        if (!disk[b].hash_valid || !ct_equal(h, disk[b].hash, HASH_LEN)) {
            ok = false;
            if (used < sz) {
                used += (size_t)snprintf(bad_list + used, sz - used, "%s%02d", used ? ", " : "", b);
            }
        }
    }
    return ok;
}

static void collect_files(FileNode* n, FileNode** out, int* cnt, int max) {
    if (!n->is_dir) {
        if (*cnt < max) out[(*cnt)++] = n;
        return;
    }
    for (int i = 0; i < n->child_count; i++) collect_files(n->children[i], out, cnt, max);
}

/* Simula um acesso direto ao dispositivo (driver/hardware): NÃO passa pelo sistema de
 * arquivos e, por isso, não atualiza o registro oficial de hash. */
void cmd_raw_disk_write(int block, const char* text) {
    ECHO("> raw_disk_write %d \"%s\"\n", block, text);
    if (!require_kernel("raw_disk_write")) return;
    if (block < 0 || block >= TOTAL_BLOCKS || disk[block].type != BLOCK_DATA) {
        printf("Erro: bloco %d inválido ou não é um bloco de dados.\n", block);
        return;
    }
    size_t len = strlen(text);
    if (len > BLOCK_SIZE) len = BLOCK_SIZE;
    memcpy(disk[block].data, text, len);
    printf("[KERNEL] Escrita direta no bloco físico %02d (sem passar pelo sistema de arquivos).\n", block);
    char obj[32];
    snprintf(obj, sizeof(obj), "bloco %02d", block);
    audit("RAW_DISK_WRITE", obj, "OK");
}

void cmd_antivirus_scan(const char* path) {
    ECHO("> antivirus_scan %s\n", path);
    if (!require_kernel("antivirus_scan")) return;

    FileNode* start = traverse_path(path);
    if (!start) { printf("Erro: caminho '%s' inexistente.\n", path); return; }

    FileNode* files[TOTAL_BLOCKS];
    int n = 0;
    collect_files(start, files, &n, TOTAL_BLOCKS);

    printf("[MÓDULO DE SEGURANÇA - VARREDURA DE INTEGRIDADE]\n");
    printf("Analisando %d arquivos em busca de assinaturas maliciosas e hashes corrompidos...\n", n);

    int width = 1;
    char paths[TOTAL_BLOCKS][MAX_PATH];
    for (int i = 0; i < n; i++) {
        node_path(files[i], paths[i], MAX_PATH);
        int len = (int)strlen(paths[i]);
        if (len > width) width = len;
    }

    int alerts = 0;
    for (int i = 0; i < n; i++) {
        const FileNode* f = files[i];
        char bad_list[96];
        bool hash_ok = file_hash_check(f, bad_list, sizeof(bad_list));

        const char* sig = NULL;
        int sig_block = -1;
        if (!f->encrypted) {      /* texto cifrado não pode ser comparado com assinaturas */
            for (int b = 0; b < f->num_data_blocks && !sig; b++) {
                for (int s = 0; s < NUM_SIGNATURES; s++) {
                    if (find_bytes(disk[f->data_blocks[b]].data, BLOCK_SIZE, MALWARE_SIGNATURES[s])) {
                        sig = MALWARE_SIGNATURES[s];
                        sig_block = f->data_blocks[b];
                        break;
                    }
                }
            }
        }

        printf("- %-*s : ", width, paths[i]);
        if (hash_ok && !sig) {
            printf("[OK - %s]\n", f->encrypted ? "Criptografado e Íntegro" : "Íntegro");
            continue;
        }

        alerts++;
        if (!hash_ok) {
            printf("[ALERTA] Hash do bloco difere do registro oficial!\n");
            printf("  Resultado: Possível modificação direta não autorizada no bloco do disco.\n");
            printf("  Bloco(s) divergente(s): %s\n", bad_list);
        }
        if (sig) {
            printf("%s[ALERTA] Assinatura maliciosa detectada: '%s' (Bloco %02d)\n",
                   hash_ok ? "" : "  ", sig, sig_block);
            printf("  Resultado: Conteúdo suspeito; arquivo sinalizado para quarentena.\n");
        }
        audit("AV_ALERTA", paths[i], "ALERTA");
    }

    printf("Resumo: %d arquivo(s) analisado(s), %d alerta(s).\n", n, alerts);
    audit("ANTIVIRUS_SCAN", path, alerts ? "ALERTA" : "OK");
}

/* ============================================================================
 * ETAPA 3.F — OPERAÇÕES DO FS COM CONTROLE DE ACESSO
 * ============================================================================ */

/* write_file "texto": regrava o conteúdo do arquivo. Toca o diretório raiz (entrada do
 * arquivo), o i-node e todos os blocos de dados. */
void write_file_fs(const char* path, const char* text) {
    ECHO("> write_file %s \"%s\"\n", path, text);
    if (!require_session()) return;

    FileNode* f = traverse_path(path);
    if (!f) {
        printf("Erro: arquivo '%s' inexistente.\n", path);
        return;
    }
    if (f->is_dir) {
        printf("Erro: '%s' é um diretório.\n", path);
        return;
    }
    if (!check_path_access(f, 'w', "ESCRITA")) return;

    if (f->encrypted) {
        printf("Erro: '%s' está criptografado; use 'decrypt_file' antes de regravar.\n", path);
        return;
    }
    if (!fs_store_bytes(f, (const uint8_t*)text, strlen(text))) {
        printf("Erro: conteúdo maior que o espaço alocado ao arquivo.\n");
        return;
    }

    io_submit_file(f, true);
    if (!echo_cmd) printf("Gravados %zu bytes em '%s'.\n", f->content_len, path);
}

/* read_file: lê o i-node e os blocos de dados (não altera o diretório). */
void read_file_fs(const char* path, const char* key) {
    if (key) ECHO("> read_file %s --key ********\n", path);
    else     ECHO("> read_file %s\n", path);
    if (!require_session()) return;

    FileNode* f = traverse_path(path);
    if (!f || f->is_dir) {
        printf("Erro: arquivo '%s' inexistente.\n", path);
        return;
    }
    if (!check_path_access(f, 'r', "LEITURA")) return;

    io_submit_file(f, false);

    char bad_list[96];
    if (!file_hash_check(f, bad_list, sizeof(bad_list))) {
        printf("[AVISO DE INTEGRIDADE] Hash do(s) bloco(s) %s difere do registro oficial: "
               "o conteúdo pode ter sido alterado fora do sistema de arquivos.\n", bad_list);
        audit("INTEGRIDADE", path, "ALERTA");
    }

    if (f->encrypted && !key) {
        printf("Conteúdo (criptografado): ");
        print_cipher_hex(f);
        printf("\nUse '--key' para decifrar a leitura.\n");
        return;
    }

    size_t len = f->content_len;
    uint8_t* buf = (uint8_t*)malloc(len + 1);
    if (!buf) { printf("Erro: sem memória.\n"); return; }
    fs_load_bytes(f, buf, len);

    if (f->encrypted) {
        if (!key_matches(f, key)) {
            free(buf);
            printf("[NEGADO]: Chave incorreta para '%s'. Tentativa registrada nos logs do sistema.\n", path);
            audit("DECRYPT", path, "NEGADO");
            return;
        }
        uint8_t dk[HASH_LEN];
        derive_file_key(f, key, dk);
        keystream_xor(dk, f->enc_nonce, buf, len);
    }

    if (len == 0) printf("Conteúdo lido: \"(vazio)\"\n");
    else          printf("Conteúdo lido: \"%.*s\"\n", (int)len, (const char*)buf);
    free(buf);
}

void cmd_chmod(const char* path, int mode) {
    ECHO("> chmod %03o %s\n", (unsigned)mode, path);
    if (!require_session()) return;

    FileNode* f = traverse_path(path);
    if (!f) { printf("Erro: '%s' inexistente.\n", path); return; }
    if (!check_ancestors(f)) return;

    if (!is_kernel() && session_user->uid != f->uid) {
        printf("[NEGADO]: Apenas o proprietário ('%s') ou o kernel podem alterar as permissões de '%s'.\n"
               "Tentativa não autorizada registrada nos logs do sistema.\n", user_name(f->uid), path);
        audit("CHMOD", path, "NEGADO");
        return;
    }

    f->mode = mode;
    char modestr[10];
    mode_to_string(mode, modestr);
    printf("Permissões de '%s' alteradas para %s (%03o).\n", path, modestr, (unsigned)mode);
    audit("CHMOD", path, "OK");
}

void cmd_chown(const char* path, const char* user, const char* group) {
    ECHO("> chown %s:%s %s\n", user, group, path);
    if (!require_kernel("chown")) return;

    FileNode* f = traverse_path(path);
    User* u = find_user(user);
    int gid = find_group(group);
    if (!f) { printf("Erro: '%s' inexistente.\n", path); return; }
    if (!u) { printf("Erro: usuário '%s' inexistente.\n", user); return; }
    if (gid < 0) { printf("Erro: grupo '%s' inexistente.\n", group); return; }

    f->uid = u->uid;
    f->gid = gid;
    printf("Proprietário de '%s' alterado para %s (Grupo: %s).\n", path, user, group);
    audit("CHOWN", path, "OK");
}

static void collect_nodes(FileNode* n, FileNode** list, int* cnt, int max) {
    if (*cnt >= max) return;
    list[(*cnt)++] = n;
    for (int i = 0; i < n->child_count; i++) collect_nodes(n->children[i], list, cnt, max);
}

/* Matriz de acesso: permissões efetivas de cada usuário sobre cada objeto. */
void cmd_access_matrix(void) {
    ECHO("> access_matrix\n");
    if (!require_kernel("access_matrix")) return;

    FileNode* list[64];
    int n = 0;
    collect_nodes(root_node, list, &n, 64);

    char paths[64][MAX_PATH];
    int width = 6;
    for (int i = 0; i < n; i++) {
        node_path(list[i], paths[i], MAX_PATH);
        int len = (int)strlen(paths[i]);
        if (len > width) width = len;
    }

    printf("[MATRIZ DE ACESSO] (permissões efetivas; root em MODO_KERNEL acessa tudo)\n");
    printf("%-*s", width, "Objeto");
    for (int u = 0; u < user_count; u++) printf("  %-8s", users[u].name);
    printf("\n");

    for (int i = 0; i < n; i++) {
        printf("%-*s", width, paths[i]);
        for (int u = 0; u < user_count; u++) {
            int bits = class_bits(&users[u], list[i]);
            char cell[4] = { (bits & 4) ? 'r' : '-', (bits & 2) ? 'w' : '-', (bits & 1) ? 'x' : '-', '\0' };
            printf("  %-8s", cell);
        }
        printf("\n");
    }
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

static PhysicalDisk raid_array[DISK_COUNT];
static int next_stripe = 0;
static int logical_raid_stripe[TOTAL_BLOCKS];
static int logical_raid_disk[TOTAL_BLOCKS];

void init_raid(void) {
    memset(raid_array, 0, sizeof(raid_array));
    for (int d = 0; d < DISK_COUNT; d++) {
        raid_array[d].disk_id = d + 1;
        raid_array[d].online = true;
    }
    next_stripe = 0;
    for (int i = 0; i < TOTAL_BLOCKS; i++) {
        logical_raid_stripe[i] = -1;
        logical_raid_disk[i] = -1;
    }
}

static int parity_disk_of(int stripe) {
    return (DISK_COUNT - 1) - (stripe % DISK_COUNT);
}

static int data_disk_of(int stripe, int k) {
    int pd = parity_disk_of(stripe);
    return (k < pd) ? k : k + 1;
}

static int raid5_stripes_needed(int blocks) {
    int data_per_stripe = DISK_COUNT - 1;
    return (blocks + data_per_stripe - 1) / data_per_stripe;
}

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

static void raid_sync_block(int logical_block) {
    if (logical_block < 0 || logical_block >= TOTAL_BLOCKS) return;
    int stripe = logical_raid_stripe[logical_block];
    int d = logical_raid_disk[logical_block];
    if (stripe < 0 || d < 0) return;
    memcpy(raid_array[d].blocks[stripe].content, disk[logical_block].data, BLOCK_SIZE);
    int parity = parity_disk_of(stripe);
    xor_stripe_except(stripe, parity, raid_array[parity].blocks[stripe].content);
}

static void raid_unlink_block(int logical_block) {
    if (logical_block < 0 || logical_block >= TOTAL_BLOCKS) return;
    int stripe = logical_raid_stripe[logical_block];
    int d = logical_raid_disk[logical_block];
    if (stripe < 0 || d < 0) return;
    PhysicalBlock* pb = &raid_array[d].blocks[stripe];
    memset(pb->content, 0, BLOCK_SIZE);
    pb->occupied = false;
    pb->label[0] = '\0';
    logical_raid_stripe[logical_block] = -1;
    logical_raid_disk[logical_block] = -1;
    int parity = parity_disk_of(stripe);
    xor_stripe_except(stripe, parity, raid_array[parity].blocks[stripe].content);
}

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
static void raid5_store_file(FileNode* file) {
    const char* filepath = file->full_path;
    int blocks_needed = file->num_data_blocks;
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

        for (int k = 0; k < data_per_stripe; k++) {
            int fb = s * data_per_stripe + k;
            if (fb >= blocks_needed) break;

            PhysicalBlock* pb = &raid_array[data_disk_of(stripe, k)].blocks[stripe];
            int logical_block = file->data_blocks[fb];
            memcpy(pb->content, disk[logical_block].data, BLOCK_SIZE);
            logical_raid_stripe[logical_block] = stripe;
            logical_raid_disk[logical_block] = data_disk_of(stripe, k);
            pb->occupied = true;
            pb->is_parity = false;
            pb->file_block = fb + 1;
            snprintf(pb->label, sizeof(pb->label), "Dados da %s - Part %d (%d KB)",
                     base, fb + 1, BLOCK_SIZE / 1024);

            off += (size_t)snprintf(parity_label + off, sizeof(parity_label) - off,
                                    "%sBloco %02d", (k == 0) ? "" : ", ", fb + 1);
        }
        snprintf(parity_label + off, sizeof(parity_label) - off, ")");

        PhysicalBlock* par = &raid_array[pd].blocks[stripe];
        xor_stripe_except(stripe, pd, par->content);
        par->occupied = true;
        par->is_parity = true;
        par->file_block = 0;
        snprintf(par->label, sizeof(par->label), "%s", parity_label);

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

/* write_file --size: cria o arquivo no FS (com checagem de ACL) e grava seus blocos no RAID 5. */
void write_file_raid5(const char* filepath, int size_kb, const char* sample_data) {
    ECHO("> write_file %s --size %dKB\n", filepath, size_kb);
    if (!require_session()) return;

    if (size_kb <= 0) {
        printf("Erro: tamanho de arquivo inválido (%d KB).\n", size_kb);
        return;
    }

    int blocks_needed = (int)(((size_t)size_kb * 1024 + BLOCK_SIZE - 1) / BLOCK_SIZE);
    if (next_stripe + raid5_stripes_needed(blocks_needed) > MAX_BLOCKS_PER_DISK) {
        printf("Erro: espaço insuficiente no arranjo RAID.\n");
        return;
    }

    FileNode* f = fs_create_file(filepath, size_kb, false);
    if (!f) return;

    /* Grava o conteúdo efetivo no sistema de arquivos antes de espelhá-lo no RAID. */
    if (sample_data && !fs_store_bytes(f, (const uint8_t*)sample_data, strlen(sample_data))) {
        printf("Erro ao gravar os dados iniciais no sistema de arquivos.\n");
        return;
    }
    raid5_store_file(f);
}

/* Falha de hardware simulada: operação crítica, só em MODO_KERNEL. */
void simulate_raid5_failure_and_reconstruction(int failed_disk_id) {
    if (!require_kernel("raid_fail")) return;

    if (failed_disk_id < 1 || failed_disk_id > DISK_COUNT) {
        printf("Erro: disco %d inexistente.\n", failed_disk_id);
        return;
    }

    int f = failed_disk_id - 1;
    static unsigned char backup[MAX_BLOCKS_PER_DISK][BLOCK_SIZE];

    printf("\n[TESTE DE FALHA SIMULADO]\n");
    printf("* Falha forçada no Disco %d!\n", failed_disk_id);

    for (int s = 0; s < next_stripe; s++) {
        memcpy(backup[s], raid_array[f].blocks[s].content, BLOCK_SIZE);
        memset(raid_array[f].blocks[s].content, 0, BLOCK_SIZE);
    }
    raid_array[f].online = false;

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
    audit("RAID_FAIL", "(arranjo RAID 5)", "OK");
}

/* ============================================================================
 * SHELL INTERATIVO (./trabalho -i)
 * ============================================================================ */

static int tokenize(char* line, char* argv[], int max) {
    int argc = 0;
    char* p = line;
    while (*p && argc < max) {
        while (*p && isspace((unsigned char)*p)) p++;
        if (!*p) break;
        if (*p == '"') {
            p++;
            argv[argc++] = p;
            while (*p && *p != '"') p++;
            if (*p) *p++ = '\0';
        } else {
            argv[argc++] = p;
            while (*p && !isspace((unsigned char)*p)) p++;
            if (*p) *p++ = '\0';
        }
    }
    return argc;
}

static bool read_secret(const char* prompt, char* out, size_t sz) {
    printf("%s", prompt);
    fflush(stdout);
    if (!fgets(out, (int)sz, stdin)) return false;
    out[strcspn(out, "\r\n")] = '\0';
    return true;
}

static void shell_help(void) {
    printf("Comandos:\n"
           "  login --user NOME | logout | whoami\n"
           "  groupadd GRUPO | useradd NOME --group GRUPO | usermod NOME --add-group GRUPO   [kernel]\n"
           "  mkdir CAMINHO | create CAMINHO TAM_KB | write_file CAMINHO \"texto\"\n"
           "  resize CAMINHO TAM_KB | delete CAMINHO (diretórios devem estar vazios)\n"
           "  write_file CAMINHO --size KB      (cria no FS e grava no RAID 5)\n"
           "  read_file CAMINHO [--key CHAVE]\n"
           "  chmod CAMINHO OCTAL | chown CAMINHO USUARIO GRUPO [kernel]\n"
           "  encrypt_file CAMINHO --key CHAVE | decrypt_file CAMINHO --key CHAVE\n"
           "  antivirus_scan CAMINHO | raw_disk_write BLOCO \"texto\" | raid_fail DISCO     [kernel]\n"
           "  tree | fs_status | show_users | show_logs | access_matrix  [kernel: últimos quatro]\n"
           "  acl_trace on|off | io_trace on|off | help | exit\n"
           "Usuário de demonstração: root / Root@2026 (MODO_KERNEL)\n");
}

static bool shell_dispatch(int argc, char* argv[]) {
    const char* cmd = argv[0];
    char pw[128];

    if (strcmp(cmd, "exit") == 0 || strcmp(cmd, "quit") == 0) return false;
    else if (strcmp(cmd, "help") == 0) shell_help();
    else if (strcmp(cmd, "login") == 0) {
        const char* name = (argc >= 3 && strcmp(argv[1], "--user") == 0) ? argv[2] : (argc >= 2 ? argv[1] : NULL);
        if (!name) { printf("Uso: login --user NOME\n"); return true; }
        if (!read_secret("Senha: ", pw, sizeof(pw))) return false;
        cmd_login(name, pw);
    }
    else if (strcmp(cmd, "logout") == 0) cmd_logout();
    else if (strcmp(cmd, "whoami") == 0) cmd_whoami();
    else if (strcmp(cmd, "groupadd") == 0 && argc >= 2) cmd_groupadd(argv[1]);
    else if (strcmp(cmd, "useradd") == 0 && argc >= 4 && strcmp(argv[2], "--group") == 0) {
        if (!require_kernel("useradd")) return true;     /* nega antes de pedir a senha */
        if (!read_secret("Senha do novo usuário: ", pw, sizeof(pw))) return false;
        cmd_useradd(argv[1], argv[3], pw);
    }
    else if (strcmp(cmd, "usermod") == 0 && argc >= 4 && strcmp(argv[2], "--add-group") == 0)
        cmd_usermod_add_group(argv[1], argv[3]);
    else if (strcmp(cmd, "mkdir") == 0 && argc >= 2) mkdir_fs(argv[1]);
    else if (strcmp(cmd, "create") == 0 && argc >= 3) create_file_fs(argv[1], atoi(argv[2]));
    else if (strcmp(cmd, "resize") == 0 && argc >= 3) update_file_fs(argv[1], atoi(argv[2]));
    else if (strcmp(cmd, "delete") == 0 && argc >= 2) delete_fs(argv[1]);
    else if (strcmp(cmd, "write_file") == 0 && argc >= 3) {
        if (strcmp(argv[2], "--size") == 0 && argc >= 4) write_file_raid5(argv[1], atoi(argv[3]), "Conteudo_Usuario");
        else write_file_fs(argv[1], argv[2]);
    }
    else if (strcmp(cmd, "read_file") == 0 && argc >= 2) {
        const char* key = (argc >= 4 && strcmp(argv[2], "--key") == 0) ? argv[3] : NULL;
        read_file_fs(argv[1], key);
    }
    else if (strcmp(cmd, "chmod") == 0 && argc >= 3) {
        char* end = NULL;
        long m = strtol(argv[2], &end, 8);
        if (*end != '\0' || m < 0 || m > 0777) printf("Erro: modo octal inválido (use 000 a 777).\n");
        else cmd_chmod(argv[1], (int)m);
    }
    else if (strcmp(cmd, "chown") == 0 && argc >= 4) cmd_chown(argv[1], argv[2], argv[3]);
    else if (strcmp(cmd, "encrypt_file") == 0 && argc >= 4 && strcmp(argv[2], "--key") == 0) cmd_encrypt_file(argv[1], argv[3]);
    else if (strcmp(cmd, "decrypt_file") == 0 && argc >= 4 && strcmp(argv[2], "--key") == 0) cmd_decrypt_file(argv[1], argv[3]);
    else if (strcmp(cmd, "antivirus_scan") == 0 && argc >= 2) cmd_antivirus_scan(argv[1]);
    else if (strcmp(cmd, "raw_disk_write") == 0 && argc >= 3) cmd_raw_disk_write(atoi(argv[1]), argv[2]);
    else if (strcmp(cmd, "raid_fail") == 0 && argc >= 2) simulate_raid5_failure_and_reconstruction(atoi(argv[1]));
    else if (strcmp(cmd, "tree") == 0) { tree_show_acl = true; show_tree_recursive(root_node, "", 1); }
    else if (strcmp(cmd, "fs_status") == 0) fs_status();
    else if (strcmp(cmd, "show_users") == 0) cmd_show_users();
    else if (strcmp(cmd, "show_logs") == 0) cmd_show_logs();
    else if (strcmp(cmd, "access_matrix") == 0) cmd_access_matrix();
    else if (strcmp(cmd, "acl_trace") == 0 && argc >= 2) { acl_trace = (strcmp(argv[1], "on") == 0); printf("acl_trace: %s\n", acl_trace ? "ligado" : "desligado"); }
    else if (strcmp(cmd, "io_trace") == 0 && argc >= 2) { io_verbose = (strcmp(argv[1], "on") == 0); printf("io_trace: %s\n", io_verbose ? "ligado" : "desligado"); }
    else printf("Comando inválido ou argumentos faltando. Digite 'help'.\n");

    return true;
}

static void run_shell(void) {
    char line[512];
    char* argv[16];

    echo_cmd = false;
    io_verbose = false;
    shell_help();

    for (;;) {
        if (session_user) printf("[%s|%s]$ ", session_user->name, is_kernel() ? "KERNEL" : "USUARIO");
        else              printf("[sem-sessão]$ ");
        fflush(stdout);
        if (!fgets(line, sizeof(line), stdin)) break;
        int argc = tokenize(line, argv, 16);
        if (argc == 0) continue;
        if (!shell_dispatch(argc, argv)) break;
    }
    printf("\n");
}

/* ============================================================================
 * CENÁRIO DE DEMONSTRAÇÃO (ETAPA 1 + EXEMPLOS 2.1, 2.2, 3.1 E 3.2)
 * ============================================================================ */

static void run_demo(void) {
    /* ---------- Sessão inicial: superusuário ---------- */
    cmd_login("root", "Root@2026");

    /* ---------- Etapa 1: sistema de arquivos ---------- */
    printf("\n=================== ETAPA 1 — SISTEMA DE ARQUIVOS ===================\n");
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

    /* =================== ETAPA 3 — SEGURANÇA =================== */
    printf("\n=================== ETAPA 3 — SEGURANÇA ===================\n");
    printf("\n--- Preparação em MODO_KERNEL: grupos, usuários e objetos protegidos ---\n");
    io_verbose = false;                      /* a partir daqui o SSTF roda em silêncio */

    cmd_groupadd("devs");
    cmd_useradd("carlos", "devs", "Carlos#123");
    cmd_useradd("ana", "admin", "Ana@Admin2026");
    cmd_show_users();

    mkdir_fs("/home");
    mkdir_fs("/home/carlos");
    mkdir_fs("/home/ana");
    cmd_chown("/home/carlos", "carlos", "devs");
    cmd_chmod("/home/carlos", 0750);
    cmd_chown("/home/ana", "ana", "admin");

    create_file_fs("/sistema/config.sys", 1);
    write_file_fs("/sistema/config.sys", "modo=producao;porta=8443;nivel_log=info");
    cmd_chmod("/sistema/config.sys", 0750);  /* root:admin rwxr-x--- */

    tree_show_acl = true;
    show_tree_recursive(root_node, "", 1);
    tree_show_acl = false;
    printf("\n");
    cmd_access_matrix();

    /* ---------- Exemplo 3.1: autenticação + ACL ---------- */
    printf("\n=================== EXEMPLO 3.1 ===================\n");
    cmd_login("carlos", "Carlos#123");
    read_file_fs("/sistema/config.sys", NULL);
    printf("\n");
    cmd_useradd("intruso", "devs", "Senha#1234");     /* operação crítica em MODO_USUARIO */

    printf("\n");
    acl_trace = true;
    cmd_login("ana", "Ana@Admin2026");                /* grupo 'admin' tem r-x no config.sys */
    read_file_fs("/sistema/config.sys", NULL);
    acl_trace = false;

    /* ---------- Exemplo 3.2: criptografia + antivírus ---------- */
    printf("\n=================== EXEMPLO 3.2 ===================\n");
    cmd_login("carlos", "Carlos#123");
    create_file_fs("/home/carlos/segredo.txt", 1);
    write_file_fs("/home/carlos/segredo.txt", "senha_do_banco=Pr0d#2026;cartao=1234-5678");
    cmd_chmod("/home/carlos/segredo.txt", 0600);
    printf("\n");
    cmd_encrypt_file("/home/carlos/segredo.txt", "MinhaChave123");
    printf("\n");
    read_file_fs("/home/carlos/segredo.txt", NULL);                 /* só o texto cifrado */
    read_file_fs("/home/carlos/segredo.txt", "MinhaChave123");      /* chave correta */
    read_file_fs("/home/carlos/segredo.txt", "ChaveErrada");        /* chave errada */

    printf("\n");
    cmd_login("ana", "Ana@Admin2026");
    create_file_fs("/home/ana/notas.txt", 1);
    write_file_fs("/home/ana/notas.txt", "lembrete: MALWARE_SIG_X1 baixado do anexo");
    read_file_fs("/home/carlos/segredo.txt", NULL);                 /* diretório do Carlos: sem 'x' */

    printf("\n");
    cmd_login("root", "Root@2026");
    cmd_raw_disk_write(2, "Registro forjado direto no disco");     /* ataque ao bloco do app.log */
    printf("\n");
    cmd_antivirus_scan("/");

    printf("\n");
    cmd_show_logs();

#ifdef EXTRA_TESTS
    printf("\n=================== TESTES EXTRAS ===================\n");
    cmd_login("carlos", "senhaerrada");
    cmd_login("fantasma", "qualquer");
    cmd_login("carlos", "Carlos#123");
    cmd_chmod("/sistema/config.sys", 0777);                          /* não é dono */
    simulate_raid5_failure_and_reconstruction(1);                    /* operação crítica */
    cmd_antivirus_scan("/");                                         /* operação crítica */
    write_file_fs("/home/carlos", "x");                              /* é diretório */
    cmd_decrypt_file("/home/carlos/segredo.txt", "ChaveErrada");
    cmd_decrypt_file("/home/carlos/segredo.txt", "MinhaChave123");
    read_file_fs("/home/carlos/segredo.txt", NULL);                  /* texto claro novamente */
    write_file_fs("/home/carlos/segredo.txt", "novo segredo");
    cmd_logout();
    read_file_fs("/home/carlos/segredo.txt", NULL);                  /* sem sessão */

    printf("\n");
    cmd_login("root", "Root@2026");
    io_verbose = true;
    read_file_fs("/sistema/logs/app.log", NULL);                     /* E/S + aviso de integridade */
    io_verbose = false;
    simulate_raid5_failure_and_reconstruction(1);
    simulate_raid5_failure_and_reconstruction(3);
    simulate_raid5_failure_and_reconstruction(2);
#endif
}

int main(int argc, char** argv) {
    security_boot();
    init_fs();
    init_raid();

    if (argc > 1 && strcmp(argv[1], "-i") == 0) {
        run_shell();
    } else {
        run_demo();
    }

    free_tree(root_node);
    return 0;
}
