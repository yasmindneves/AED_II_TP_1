#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#define INIT_PRIME 101       
#define LOAD_MAX 0.75        
#define DESC_MAX 60
#define CODE_MAX 64


typedef struct {
    char codigo[CODE_MAX];
    char descricao[DESC_MAX + 1];
    int qtde;
    float preco;
} Item;

typedef struct Node {
    Item item;
    struct Node* next;
} Node;


typedef enum {
    HASH_DIVISAO = 0,
    HASH_MULTIPLICACAO = 1,
    HASH_DOBRA = 2
} HashMethod;


typedef struct {
    Node** buckets;
    size_t m;               
    size_t n;                
    HashMethod method;        
    unsigned long long total_buscas; 
    unsigned long long total_comp;  
} HashTable;


static int is_prime(size_t x) {
    if (x < 2) return 0;
    if (x % 2 == 0) return x == 2;
    for (size_t i = 3; i * i <= x; i += 2)
        if (x % i == 0) return 0;
    return 1;
}

static size_t next_prime(size_t x) {
    if (x <= 2) return 2;
    if (x % 2 == 0) x++;
    while (!is_prime(x)) x += 2;
    return x;
}

static void trim_newline(char* s) {
    if (!s) return;
    size_t len = strlen(s);
    if (len && (s[len-1] == '\n' || s[len-1] == '\r')) s[len-1] = '\0';
}

static void read_line(const char* prompt, char* buf, size_t cap) {
    if (prompt) printf("%s", prompt);
    if (fgets(buf, (int)cap, stdin) == NULL) {
        buf[0] = '\0';    // EOF
        return;
    }
    trim_newline(buf);
}

static int str_case_equal(const char* a, const char* b) {
    while (*a && *b) {
        unsigned char ca = (unsigned char)*a++;
        unsigned char cb = (unsigned char)*b++;
        ca = (unsigned char)tolower(ca);
        cb = (unsigned char)tolower(cb);
        if (ca != cb) return 0;
    }
    return *a == '\0' && *b == '\0';
}

static HashTable* ht_create(size_t m, HashMethod h) {
    HashTable* ht = (HashTable*)malloc(sizeof(HashTable));
    if (!ht) {
        fprintf(stderr, "Falha ao alocar HashTable.\n");
        exit(1);
    }
    ht->m = m;
    ht->n = 0;
    ht->method = h;
    ht->total_buscas = 0ULL;
    ht->total_comp = 0ULL;
    ht->buckets = (Node**)calloc(ht->m, sizeof(Node*));
    if (!ht->buckets) {
        fprintf(stderr, "Falha ao alocar buckets.\n");
        free(ht);
        exit(1);
    }
    return ht;
}

static void ht_free(HashTable* ht) {
    if (!ht) return;
    for (size_t i = 0; i < ht->m; ++i) {
        Node* cur = ht->buckets[i];
        while (cur) {
            Node* nx = cur->next;
            free(cur);
            cur = nx;
        }
    }
    free(ht->buckets);
    free(ht);
}

static unsigned long long str_key_polynomial(const char* s) {
    const unsigned long long B = 131ULL;
    unsigned long long h = 0ULL;
    for (const unsigned char* p = (const unsigned char*)s; *p; ++p)
        h = h * B + (unsigned long long)(*p);
    return h;
}

static size_t hash_divisao(size_t m, const char* codigo) {
    unsigned long long k = str_key_polynomial(codigo);
    return (size_t)(k % (unsigned long long)m);
}

static size_t hash_multiplicacao(size_t m, const char* codigo) {
    unsigned long long k = str_key_polynomial(codigo);
    const long double A = 0.6180339887498948482L; // (v5 - 1)/2
    long double frac = (k * A) - (unsigned long long)(k * A);
    if (frac < 0.0L) frac = -frac;
    size_t idx = (size_t)((long double)m * frac);
    if (idx >= m) idx = m - 1;
    return idx;
}

static size_t hash_dobra(size_t m, const char* codigo) {
    unsigned long long acc = 0ULL;
    size_t len = strlen(codigo);
    for (size_t i = 0; i < len; i += 4) {
        unsigned long long bloco = 0ULL;
        for (size_t j = 0; j < 4 && i + j < len; ++j)
            bloco = (bloco << 8) | (unsigned long long)(unsigned char)codigo[i + j];
        acc += bloco;
    }
    return (size_t)(acc % (unsigned long long)m);
}

static size_t ht_index(const HashTable* ht, const char* codigo) {
    switch (ht->method) {
        case HASH_DIVISAO:        return hash_divisao(ht->m, codigo);
        case HASH_MULTIPLICACAO:  return hash_multiplicacao(ht->m, codigo);
        case HASH_DOBRA:          return hash_dobra(ht->m, codigo);
        default:                  return hash_divisao(ht->m, codigo);
    }
}

static Node* bucket_find(Node* head, const char* codigo, unsigned long long* comps) {
    Node* cur = head;
    while (cur) {
        if (comps) (*comps)++;
        if (strcmp(cur->item.codigo, codigo) == 0) return cur;
        cur = cur->next;
    }
    return NULL;
}

static void ht_rehash(HashTable* ht, size_t new_m) {
    Node** old_b = ht->buckets;
    size_t old_m = ht->m;

    Node** new_b = (Node**)calloc(new_m, sizeof(Node*));
    if (!new_b) {
        fprintf(stderr, "Falha ao alocar buckets no rehash.\n");
        return;
    }

    ht->buckets = new_b;
    ht->m = new_m;
    ht->n = 0;

    for (size_t i = 0; i < old_m; ++i) {
        Node* cur = old_b[i];
        while (cur) {
            Node* nx = cur->next;
            size_t idx = ht_index(ht, cur->item.codigo);
            cur->next = ht->buckets[idx];
            ht->buckets[idx] = cur;
            ht->n++;
            cur = nx;
        }
    }
    free(old_b);
}

static double ht_load_factor(const HashTable* ht) {
    if (ht->m == 0) return 0.0;
    return (double)ht->n / (double)ht->m;
}

static int ht_insert(HashTable* ht, const Item* it) {
    size_t idx = ht_index(ht, it->codigo);
    if (bucket_find(ht->buckets[idx], it->codigo, NULL) != NULL)
        return 0; // duplicado

    Node* node = (Node*)malloc(sizeof(Node));
    if (!node) return 0;
    node->item = *it;
    node->next = ht->buckets[idx];
    ht->buckets[idx] = node;
    ht->n++;

    // rehash se alpha > LOAD_MAX
    if (ht_load_factor(ht) > LOAD_MAX) {
        size_t novo_m = next_prime(ht->m * 2 + 1);
        ht_rehash(ht, novo_m);
    }
    return 1;
}

static int ht_search(HashTable* ht, const char* codigo, Item* out) {
    size_t idx = ht_index(ht, codigo);
    unsigned long long comps = 0ULL;
    Node* n = bucket_find(ht->buckets[idx], codigo, &comps);
    ht->total_buscas++;
    ht->total_comp += comps;
    if (!n) return 0;
    if (out) *out = n->item;
    return 1;
}

static int ht_remove(HashTable* ht, const char* codigo) {
    size_t idx = ht_index(ht, codigo);
    Node* cur = ht->buckets[idx];
    Node* prev = NULL;
    while (cur) {
        if (strcmp(cur->item.codigo, codigo) == 0) {
            if (prev) prev->next = cur->next;
            else ht->buckets[idx] = cur->next;
            free(cur);
            ht->n--;
            return 1;
        }
        prev = cur;
        cur = cur->next;
    }
    return 0;
}


static void ht_stats(const HashTable* ht, size_t* used, size_t* maxlist) {
    size_t u = 0, ml = 0;
    for (size_t i = 0; i < ht->m; ++i) {
        size_t len = 0;
        Node* cur = ht->buckets[i];
        if (cur) u++;
        while (cur) {
            len++;
            cur = cur->next;
        }
        if (len > ml) ml = len;
    }
    if (used) *used = u;
    if (maxlist) *maxlist = ml;
}

static const char* method_name(HashMethod h) {
    switch (h) {
        case HASH_DIVISAO:       return "Divisao";
        case HASH_MULTIPLICACAO: return "Multiplicacao";
        case HASH_DOBRA:         return "Dobra";
        default:                 return "Desconhecido";
    }
}

/* ======= CSV ======= */

static int parse_csv_line(char* line, Item* it) {
    const char* sep = ";\n\r";
    char* t1 = strtok(line, sep);
    if (!t1) return 0;
    char* t2 = strtok(NULL, sep);
    if (!t2) return 0;
    char* t3 = strtok(NULL, sep);
    if (!t3) return 0;
    char* t4 = strtok(NULL, sep);
    if (!t4) return 0;

    strncpy(it->codigo, t1, CODE_MAX - 1);
    it->codigo[CODE_MAX - 1] = '\0';
    strncpy(it->descricao, t2, DESC_MAX);
    it->descricao[DESC_MAX] = '\0';
    it->qtde = atoi(t3);
    it->preco = (float)strtod(t4, NULL);
    return 1;
}

static int ht_load_csv(HashTable* ht, const char* fname) {
    FILE* f = fopen(fname, "r");
    if (!f) {
        printf("Erro: nao foi possivel abrir %s.\n", fname);
        return -1;
    }
    char line[512];
    int count = 0;
    int first = 1;
    while (fgets(line, sizeof(line), f)) {
        trim_newline(line);
        if (line[0] == '\0') continue;
        if (first) {
            first = 0;
            if (str_case_equal(line, "codigo;descricao;qtde;preco"))
                continue;
        }
        Item it;
        char work[512];
        strncpy(work, line, sizeof(work)-1);
        work[sizeof(work)-1] = '\0';
        if (parse_csv_line(work, &it)) {
            if (ht_insert(ht, &it))
                count++;
        }
    }
    fclose(f);
    return count;
}

static int ht_save_csv(const HashTable* ht, const char* fname) {
    FILE* f = fopen(fname, "w");
    if (!f) {
        printf("Erro: nao foi possivel abrir %s para escrita.\n", fname);
        return 0;
    }
    fprintf(f, "codigo;descricao;qtde;preco\n");
    for (size_t i = 0; i < ht->m; ++i) {
        Node* cur = ht->buckets[i];
        while (cur) {
            const Item* it = &cur->item;
            fprintf(f, "%s;%s;%d;%.2f\n", it->codigo, it->descricao, it->qtde, it->preco);
            cur = cur->next;
        }
    }
    fclose(f);
    return 1;
}

static void ht_switch_method(HashTable* ht) {
    ht->method = (HashMethod)((((int)ht->method) + 1) % 3);
    size_t m_atual = ht->m;
    ht_rehash(ht, m_atual);
    printf("Funcao hash alterada para %s.\n", method_name(ht->method));
    printf("Rehash automatico realizado. Tamanho da tabela: %zu.\n", ht->m);
}


static void menu_inserir(HashTable* ht) {
    Item it;
    char buf[256];

    printf("[1] Inserir nova peca\n");
    read_line("codigo: ", it.codigo, sizeof(it.codigo));
    read_line("descricao: ", it.descricao, sizeof(it.descricao));
    read_line("qtde: ", buf, sizeof(buf));
    it.qtde = atoi(buf);
    read_line("preco: ", buf, sizeof(buf));
    it.preco = (float)strtod(buf, NULL);

    if (ht_insert(ht, &it))
        printf("Peca %s inserida com sucesso.\n", it.codigo);
    else
        printf("Erro: ja existe uma peca cadastrada com o codigo %s.\n", it.codigo);
}

static void menu_buscar(HashTable* ht) {
    char codigo[CODE_MAX];
    printf("[2] Buscar peca por codigo\n");
    read_line("codigo: ", codigo, sizeof(codigo));
    Item it;
    if (ht_search(ht, codigo, &it)) {
        printf("Peca encontrada:\n");
        printf("Codigo: %s\n", it.codigo);
        printf("Descricao: %s\n", it.descricao);
        printf("Quantidade: %d\n", it.qtde);
        printf("Preco: %.2f\n", it.preco);
    } else {
        printf("Nenhuma peca encontrada com o codigo informado.\n");
    }
}

static void menu_remover(HashTable* ht) {
    char codigo[CODE_MAX];
    printf("[3] Remover peca do estoque\n");
    read_line("codigo: ", codigo, sizeof(codigo));
    if (ht_remove(ht, codigo))
        printf("Peca %s removida com sucesso.\n", codigo);
    else
        printf("Erro: nao foi encontrada peca com o codigo %s.\n", codigo);
}

static void menu_estatisticas(HashTable* ht) {
    size_t used = 0, maxlist = 0;
    ht_stats(ht, &used, &maxlist);
    double alpha = ht_load_factor(ht);
    printf("[4] Exibir estatisticas da tabela\n");
    printf("Tamanho da tabela (m): %zu\n", ht->m);
    printf("Numero de itens (n): %zu\n", ht->n);
    printf("Fator de carga (alpha): %.3f\n", alpha);
    printf("Buckets utilizados: %zu (%.2f%%)\n",
           used, (100.0 * (double)used / (double)ht->m));
    printf("Maior lista (colisoes): %zu\n", maxlist);
    printf("Metodo de hash: %s\n", method_name(ht->method));
    if (ht->total_buscas > 0ULL) {
        double media = (double)ht->total_comp / (double)ht->total_buscas;
        printf("Media de comparacoes (buscas realizadas): %.3f\n", media);
    } else {
        printf("Media de comparacoes: sem buscas realizadas ainda.\n");
    }
}

static void menu_carregar_csv(HashTable* ht) {
    char fname[256];
    printf("[5] Carregar pecas de um arquivo CSV\n");
    read_line("arquivo: ", fname, sizeof(fname));
    int loaded = ht_load_csv(ht, fname);
    if (loaded >= 0)
        printf("%d itens carregados de %s\n", loaded, fname);
}

static void menu_salvar_csv(HashTable* ht) {
    char fname[256];
    printf("[6] Salvar tabela em arquivo CSV\n");
    read_line("arquivo: ", fname, sizeof(fname));
    if (ht_save_csv(ht, fname))
        printf("Tabela salva em %s\n", fname);
}

int main(void) {
    HashTable* ht = ht_create(INIT_PRIME, HASH_DIVISAO);

    int opcao = 0;
    char buf[64];

    do {
        printf("===========================================\n");
        printf(" SISTEMA DE ESTOQUE - TECHPARTS\n");
        printf("===========================================\n\n");
        printf("[1] Inserir nova peca\n");
        printf("[2] Buscar peca por codigo\n");
        printf("[3] Remover peca do estoque\n");
        printf("[4] Exibir estatisticas da tabela\n");
        printf("[5] Carregar pecas de um arquivo CSV\n");
        printf("[6] Salvar tabela em arquivo CSV\n");
        printf("[7] Trocar funcao de hash (Divisao <-> Multiplicacao <-> Dobra)\n");
        printf("[8] Encerrar o programa\n\n");
        printf("Digite a opcao desejada: ");

        if (!fgets(buf, sizeof(buf), stdin)) break;
        opcao = atoi(buf);

        switch (opcao) {
            case 1: menu_inserir(ht); break;
            case 2: menu_buscar(ht); break;
            case 3: menu_remover(ht); break;
            case 4: menu_estatisticas(ht); break;
            case 5: menu_carregar_csv(ht); break;
            case 6: menu_salvar_csv(ht); break;
            case 7: ht_switch_method(ht); break;
            case 8: printf("Encerrando o sistema... ate logo!\n"); break;
            default: printf("Opcao invalida.\n"); break;
        }
        printf("\n");
    } while (opcao != 8);

    ht_free(ht);
    return 0;
}
