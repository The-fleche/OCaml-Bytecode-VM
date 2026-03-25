#include <errno.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include "objets.h"

// on prend une taille de pile arbitraire
// assez grande car on ne sait pas à l'avance la taille maximale nécessaire

#define Max 1000

typedef struct pile {
    long data[Max];
    int top;
} pile;


/*  @requires pile : p une pile
    @assigns None
    @ensures affiche les éléments de la pile avec un saut de 
    ligne entre chaque élément
    */
void affich_pile(pile *p) {
    printf("Stack: \n");
    for(int i=0; i < p->top; i++) {
        printf("%ld \n", p->data[i]);
    }
    printf("\n");
}


// Initialisation pile vide

void init_pile(pile *p){
    p->top=-1;
}

// Test de vacuité

int vacuite_test(pile *p) {
    if (p->top == -1) {
        return 1;
    } else {
        return 0;
    }
}

// Empilement 

// void empile(pile *p, int val){
//     p->top += 1;
//     p->data[p->top] = val;
// }

long empile(pile *p, long val){
    if (p->top>=Max-1) return -1;
    p->top+=1;
    // printf("top incrémenté : %d\n", p->top);
    p->data[p->top] = val;
    return 0;
}

// dépilement 


long depile(pile *p, int *erreur){
    if (p->top < 0) {
        *erreur = 1; // Signal d'erreur
        return 0;
    }
    *erreur = 0; // Tout va bien
    p->top--;
    return p->data[p->top+1];
}