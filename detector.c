//////////////////////////////////////////////////////////////////////////////////
// AUTHOR:   Robert Morouney <069001422>
// EMAIL:    robert@morouney.com
// FILE:     detector.c
// CREATED:  2018-11-09 02:02:29
// MODIFIED: 2018-11-09 08:09:01
//////////////////////////////////////////////////////////////////////////////////

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint32_t u32;
typedef uint8_t u8;
typedef uint32_t ** m32;
typedef uint32_t * v32;
typedef bool* boolv;

m32 init_m32(size_t, u32);
v32 init_v32(size_t);
boolv init_vbool(size_t n);
void free_m32(size_t, m32);
void print_boolv(size_t m, bool f[m]);
void print_vbool(size_t n, bool b[n]);
void print_v32(size_t m, u32 v[m]);

int line2vec(FILE*, size_t, v32);
u32 detect(size_t, size_t, m32, m32, v32, v32, boolv, u32*, boolv, u32*);
int recover(size_t, size_t, m32, m32, v32, v32, boolv, u32*, boolv, u32*);


int main(/* dont care */)
{
    size_t n, m;
    { /* read first line to m and n */
        v32 t = init_v32(2);
        line2vec(stdin,2,t);
        n = (size_t)t[0];
        m = (size_t)t[1];
        free(t);
        assert(n&&m);
    }

    { /* declare matricies */
        m32 R, A;
        v32 U, O;
        boolv K, F;
        { /* init the matricies */
/*+*/       R =  init_m32(n,m);
/*+*/       A =  init_m32(n,m);
/*+*/       U =  init_v32(m);
/*+*/       O =  init_v32(n);
/*+*/       K =  init_vbool(n);
/*+*/       F =  init_vbool(n);
        }

        { /* read the remaining 2n + 1 lines */
            u32 i,j;
            for(i = 0; i < n; i++ ) line2vec(stdin, m, R[i]);
            for(i = 0; i < n; i++ ) line2vec(stdin, m, A[i]);
            line2vec(stdin, m, U);
        }

        u32 fin = 0, kil = 0;
        u32 deadlocks = detect(n,m,R,A,U,O,F,&fin,K,&kil);
        if(deadlocks)
        {
            print_boolv(n,F);
            recover(n,m,R,A,U,O,F,&fin,K,&kil);
            print_vbool(n,K);
        }

        print_v32(m,O);

/*-*/   free_m32(n, R);
/*-*/   free_m32(n, A);
/*-*/   free(U);
/*-*/   free(O);
/*-*/   free(K);
/*-*/   free(F);
    }

    return 0;
}

v32 cpy_v32(size_t m, v32 v)
{
    v32 t = init_v32(m);
    u32 i;
    for(i=0;i<m;i++)
        t[i]=v[i];
    return t;
}

void add_v32 (size_t m, v32 src, v32 dst)
{
    u32 i;
    for(i = 0; i < m; i++)
        dst[i] += src[i];
}

size_t remove_trailing_chars (size_t len, char line[len])
{
    size_t bytes_removed = 0U;
    while ( len > 0U && line[--len] &&
      (line[len] < 0x30U || line[len] > 0x7EU) &&
      ++bytes_removed )
        line[len] = '\0';
    return bytes_removed;
}

#define SBUFF 1024
#define _SETUP(t,b,d) t = strtok(b,d)
#define _ADVANCE(t,d) t = strtok(NULL,d)
int line2vec(FILE* fp, size_t m, u32 v[m])
{
    char buffer[SBUFF];
    if(fgets(buffer, SBUFF, fp))
    {
        size_t line_len = strlen(buffer);
        line_len -= remove_trailing_chars(line_len, buffer);
        char * token;
        const char * delim = " ";
        _SETUP(token,buffer,delim);
        u32 i;
        for(i = 0; i < m; i++)
        {
            assert(token != NULL && token[0] != '\0');
            v[i] = atoi(token);
            if(v[i] == 0) assert(token[0] == 0x30);
            _ADVANCE(token, delim);
        }
    } else goto errr;

    return 0;
errr:
    fprintf(stderr,"No data from fgets() in line2vec\n"
    "\tcurrent buffer=%s\n",buffer);
    exit(EXIT_FAILURE);
}
#undef _SETUP
#undef _ADVANCE
#undef SBUFF

bool cmpv(u32 m, u32 v[m], u32 y[m])
{
    u32 i;
    for(i=0; i<m; i++)
        if(v[i] > y[i]) return false;
    return true;
}

u32 detect(size_t n, size_t m, m32 R, m32 A, v32 U,
           v32 O, boolv f, u32* e, boolv K, u32* k)
{ /* algorithm from Unit04 slide 52/54 CP386 FALL 2018 */
    u32 p, t=*e+*k;
    for(p=0; p<n; p++)
    {
        u32 i;
        for(i=0; i<n; i++)
        {
            if(!K[i] && !f[i] && cmpv(m,R[i],U))
            {
                add_v32(m,A[i],U);
                f[i] = true;
                O[(*e)++] = (i + 1);
                t++;
                //break; /* This is MORE than a typo!! */
            }
        }
        if (t == n) return 0;
    }
    return (n - t);

errr:
    fprintf(stderr,"deadlock function error\n");
    exit(EXIT_FAILURE);
}

int recover(size_t n, size_t m, m32 R, m32 A, v32 U,
            v32 O, boolv F, u32* e, boolv K, u32* k)
{
    u32 d;
    do
    {
        u32 i = 0;
        while(i<n && (F[i] || K[i])) i++;
        if(i != n)
        {
            (*k)++;
            K[i] = true;
            F[i] = false;
            add_v32(m,A[i], U);
            free(A[i]);
            A[i] = init_v32(m);
            free(R[i]);
            R[i] = init_v32(m);
        } else break;
        d = detect(n,m,R,A,U,O,F,e,K,k);
    }while(d);
    return 0;
}

m32 init_m32(size_t n, u32 m){
    m32 t = malloc(n*sizeof(v32));
    assert(t!=NULL);
    u32 i;
    for (i = 0; i < n; i++)
        t[i] = init_v32(m);
    return t;
}

v32 init_v32(size_t n){
    v32 t = calloc(n,sizeof(u32));
    return t;
}

boolv init_vbool(size_t n)
{
    boolv t = calloc(n,sizeof(bool));
    return t;
}

void free_m32(size_t n, m32 M){
    size_t i;
    for(i=0;i<n;i++)
        if(M[i]) free(M[i]);
    if (M!=NULL) free(M);
}

void print_boolv(size_t m, bool f[m])
{
    size_t i;
    for(i=0;i<m;i++)
        if(!f[i])
            printf("%lu%c", i+1, i+1==m?'\0':' ');
    printf("\n");
}
void print_vbool(size_t n, bool b[n])
{
    size_t i;
    for(i = 0; i < n; i++)
        if(b[i]) printf("%lu%c",i+1,i+1==n?'\0':' ');
    printf("\n");
}
void print_v32(size_t m, u32 v[m])
{
    size_t i;
    for(i=0;i<m;i++)
        if(v[i])
            printf("%u%c", v[i], i+1==m?'\0':' ');
    printf("\n");
}