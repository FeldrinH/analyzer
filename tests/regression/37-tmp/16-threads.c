//PARAM: --enable ana.library --sets ana.activated[-] threadid  --sets ana.activated[+] mallocWrapperTypeBased --sets ana.activated[-] mallocWrapper --sets ana.activated[+] writtenLvals --sets ana.activated[+] typecasts

#include <assert.h>
#include <stdarg.h>
#include <pthread.h>

void *foo(void *x){
    int* i = (int*) x;
    int top;
    if(top){
        *i = *i + 1;
    }
    return x;
}

int main(){
    pthread_t thread;
    int v = 10;
    assert(v == 10);
    void* ptr = &v;
    foo(ptr);
    pthread_create(&thread, NULL, foo, ptr);
    pthread_join(thread, NULL);
    assert(v == 10); //UNKNOWN!
    return 0;
}
