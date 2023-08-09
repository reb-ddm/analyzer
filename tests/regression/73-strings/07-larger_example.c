// PARAM: --disable ana.base.limit-string-addresses --enable ana.int.interval --enable ana.base.arrays.nullbytes

#include <goblint.h>
#include <string.h>
#include <stdlib.h>

int main() {
    char* user;
    if (rand())
        user = "Alice";
    else
        user = "Bob";

    if (strcmp(user, "Alice") == 0)
        strcpy(user, "++++++++"); // WARN

    char pwd_gen[20];
    for (size_t i = 12; i < 20; i++)
        pwd_gen[i] = (char) (rand() % 123);
    
    char* p1 = "hello";
    char* p2 = "12345";
    strcat(pwd_gen, p1); // WARN
    strncpy(pwd_gen, p2, 6);
    __goblint_check(pwd_gen[5] == '\0'); // TODO: fix get in attributeconfiguredarraydomain
    strncat(pwd_gen, p1, 4); 
    __goblint_check(pwd_gen[5] != '\0'); // TODO: fix get in attributeconfiguredarraydomain

    pwd_gen[10] = '\0';
    int cmp = strcmp(pwd_gen, "12345hello");
    __goblint_check(cmp != 0);

    char* pwd = strstr(pwd_gen, p2);
    size_t pwd_len = strlen(pwd_gen);
    __goblint_check(pwd_len == 9);

    return 0;
}
