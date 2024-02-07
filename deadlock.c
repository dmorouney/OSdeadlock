#include <assert.h>
#include <errno.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>


#define DEBUG 0

 /* typedefs to make my life easier */
    typedef uint32_t u32;
    typedef uint8_t u8;
    typedef uint32_t ** m32;
    typedef uint32_t * v32;
    typedef bool* boolv;

    static const u32 sgt = 0xDead10cC;

    m32 init_m32(u32, u32);
    v32 init_v32(u32);
    boolv init_vbool(u32 n);
    void free_m32(u32, m32);
    void free_v3(v32);
    void print_boolv(size_t m, bool f[m]);
    void print_v32(u32 m, u32 v[m]);

int line2vec(FILE*, u32, v32);
u32 detect(u32, u32, m32, m32, v32, v32, boolv, boolv, u32);
int recover(u32, u32, m32, m32, v32, v32, boolv, boolv);


int main(/* dont care */)
{
    u32 n, m; 
    { /* read first line to m and n */
        v32 t = init_v32(2);
        line2vec(stdin,2,t);
        n = t[0]; 
        m = t[1];
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
/*+*/       O =  init_v32(n); /* keep an order of when procs finish */
/*+*/       K =  init_vbool(n); /* order to kill procs */
/*+*/       F =  init_vbool(n);
        }
        
        { /* read the remaining 2n + 1 lines */
            u32 i,j;
            for(i = 0; i < n; i++ ) line2vec(stdin, m, R[i]);
            for(i = 0; i < n; i++ ) line2vec(stdin, m, A[i]);
            line2vec(stdin, m, U);
        }

        u32 deadlocks = detect(n,m,R,A,U,O,F,K,0);
        if(deadlocks)
        {
            print_boolv(n,F);
            void print_vbool(u32 n, bool b[n])
            {
                size_t i;
                for(i = 0; i < n; i++) 
                    if(b[i]) printf("%u%c",i+1,i+1==n?'\0':' ');
                printf("\n");
            }
            recover(n,m,R,A,U,O,F,K,deadlocks);
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




bool cmp_v32(u32 len, v32 v1, v32 v2, bool (*op)(u32, u32))
{   
    u32 i;
    for(i = 0; i < len; i++)
        if (!((*op)(v1[i],v2[i]))) return false;
    return true;

}

/* outfix */
    bool lt (u32 x, u32 y)   { return x < y;  }
    bool gt (u32 x, u32 y)   { return x > y;  }
    bool eq (u32 x, u32 y)   { return x == y; }
    bool lteq (u32 x, u32 y) { return x <= y; }
    bool gteq (u32 x, u32 y) { return x >= y; }

v32 cpy_v32(u32 m, v32 v)
{
    v32 t = init_v32(m);
    u32 i;
    for(i=0;i<m;i++)
        t[i]=v[i];
    return t;
}

void add_v32 (u32 m, v32 src, v32 dst)
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
int line2vec(FILE* fp, u32 m, v32 v)
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

u32 detect(u32 n, u32 m, m32 R, m32 A, v32 U, v32 O, boolv f, boolv K, u32 killed)
{ /* algorithm from Unit04 slide 52/54 CP386 FALL 2018 */
    v32 T;
    u32 finished = 0;
/*+*/   T = cpy_v32(m,U);


    bool cmpv(u32 m, u32 v[m], u32 y[m])
    {
        u32 i;
        for(i=0; i<m; i++)
            if(v[i] > y[i]) return false;
        return true;
    }
    { /* Can each process finish? */
        u32 p;
        for(p=0; p<n; p++)
        {
            u32 i;
            for(i=0; i<n; i++)
            {
                if(!K[i] && !f[i] && cmp_v32(m,R[i],T, lteq))
                {
                    add_v32(m,A[i],T);
                    f[i] = true;
                    O[finished++] = (i + 1);
                    break;
                }
            }
            if (finished == n) break;
        }
    }
/*-*/    free(T);
  
    return (n - (finished + killed));

errr:
    fprintf(stderr,"deadlock function error\n");
    exit(EXIT_FAILURE);
}

int recover(u32 n, u32 m, m32 R, m32 A, v32 U, v32 O, boolv F, boolv K)
{
    u32 d;
    u32 killed = 0;
    for(d=0; d<n; d++)
    {
        u32 i = 0;
        while(i<n && (K[i] || F[i])) i++;
        if(i!=n)
        {
            killed++;
            K[i] = true;
            add_v32(m,A[i], U);
            free(A[i]);
            A[i] = init_v32(m);
            u32 _ = detect(n,m,R,A,U,O,F,K,killed);
        }
    }
    return 0;
}


/* garbage functions */

m32 init_m32(u32 n, u32 m){
    m32 t = malloc(n*sizeof(v32));
    assert(t!=NULL);
    u32 i;
    for (i = 0; i < n; i++)
        t[i] = init_v32(m);
    return t;
}

v32 init_v32(u32 n){
    v32 t = calloc(n,sizeof(u32));
    return t;
}

boolv init_vbool(u32 n)
{
    boolv t = calloc(n,sizeof(bool));
    return t;
}

void free_m32(u32 n, m32 M){
    u32 i;
    for(i=0;i<n;i++)
        if(M[i]) free(M[i]);
    if (M!=NULL) free(M);
}

void print_boolv(u32 m, bool f[m])
{
    u32 i;
    for(i=0;i<m;i++)
        if(!f[i]) 
            printf("%u%c", i+1, i+1==m?'\0':' ');
    printf("\n");
}
            
void print_v32(u32 m, u32 v[m])
{
    u32 i;
    for(i=0;i<m;i++)
        if(DEBUG || v[i]) 
            printf("%u%c", v[i], i+1==m?'\0':' ');
    printf("\n");
}