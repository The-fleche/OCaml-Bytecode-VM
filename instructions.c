#include <stdio.h>
#include <stdlib.h>
#include "instructions.h"
#include "objets.h"

#define Max 1000

typedef struct pile {
    long data[Max];
    int top;
} pile;


struct virtual_machine {
    unsigned int c; // nombre de codes dans le tableau de codes
    unsigned int v; // nombre de valeurs dans le tableau de valeurs globales

    int* codes; // tableau des codes
    long* valeurs; // tableau des valeurs globales

    unsigned int indice; // indice courant dans le tableau de codes
    long accu; // accumulateur
    int running; // 1 ou 0 selon l'état de la machine virtuelle

    pile p; // pile de valeurs
}; 

typedef struct virtual_machine vim;

// Définitions variables globalement

void* atomes[256]; // tableau global des atomes
int true = 1;
int false = 0;

// fonctions utilitaires

/*  @requires   n : un entier
    @assigns    rien
    @ensures    retourne la valeur encodée de n
*/
long encode(long n) {
    return 2*n + 1;
}

/*  @requires   n : un entier encodé
    @assigns    rien
    @ensures    retourne la valeur décodée de n
*/
long decode(long n) {
    return (n - 1) / 2;
}

/*  @requires   n : un entier
    @assigns    rien
    @ensures    retourne la valeur absolue de n
*/
long abs_long(long n) {
    if (n < 0) {
        return -n;
    } else {
        return n;
    }
}

void init_atomes() {
    for (int i=0; i < 256; i++) {
        atomes[i] = malloc(0); // les atomes sont représentés par des blocs de taille 0
        if (atomes[i] == NULL) {
            fprintf(stderr, "[init_atomes] Erreur d'allocation mémoire pour le tableau des atomes.\n");
            exit(1);
        } // obligé de passer par une variable tempon pour retirer le warning
        
    }
}

void free_atomes() {
    for (int i=0; i < 256; i++) {
        free(atomes[i]);        
    }
}



////////////////////// Instructions de bases /////////////////////////////////



/*  @requires   vm : machine virtuelle valide 
                vm->p une pile non vide
    @assigns    vm->accu ; vm->indice ; vm->running
    @ensures    l'accumulateur contient la valeur au sommet de la pile
                vm->indice incrémenté de 1
*/
void ACC0(vim *vm) {
    // on vérifie que la pile est non vide avant de prendre une valeur 
    // qu'elle contient 
    if (vacuite_test(&vm->p)) {
        fprintf(stderr, "[ACC0] Pile vide\n");
        vm->running = 0; // on arrête la machine virtuelle en cas d'erreur
        return;
    } 
    vm->accu = vm->p.data[vm->p.top];
    // on incrémente l'indice de 1 pour passer à l'instruction suivante
    vm->indice++;
}

/*  @requires   vm : machine virtuelle valide 
                vm->p une pile de profondeur minimale n
    @assigns    vm->accu ; vm->indice ; vm->running
    @ensures    vm->accu contient la valeur à la profondeur n de la pile
                vm->indice incrémenté de 1
*/
void ACCN(vim *vm, int n) {
    // printf("top : %d    %d\n ", vm->p.top, n);
    if (vm->p.top < n) {
        fprintf(stderr, "[ACC%d] Pile de profondeur insuffisante\n", n);
        vm->running = 0; // on arrête la machine virtuelle en cas d'erreur
        return;
    } else {
        vm->accu = vm->p.data[vm->p.top - n];
    }
    // on incrémente l'indice de 1 pour passer à l'instruction suivante
    vm->indice++;
}

// Application rapide de ACCN avec N = n \in [| 1 ; 7 |]
void ACC1(vim *vm) {ACCN(vm, 1);}
void ACC2(vim *vm) {ACCN(vm, 2);}
void ACC3(vim *vm) {ACCN(vm, 3);}  
void ACC4(vim *vm) {ACCN(vm, 4);}
void ACC5(vim *vm) {ACCN(vm, 5);}
void ACC6(vim *vm) {ACCN(vm, 6);}
void ACC7(vim *vm) {ACCN(vm, 7);}

/*  @requires   vm : machine virtuelle valide 
                vm->p une pile de profondeur minimale n (valeur suivante du tableau de code)
    @assigns    vm->accu ; vm->indice ; vm->running
    @ensures    vm->accu contient la valeur à la profondeur n de la pile
                vm->indice est incrémenté de 2
*/
void ACC(vim *vm) {
    // on vérifie qu'il n'y a pas de dépassement
    // vm->indice ne peut pas être négatif car il est du type unsigned int 
    if (vm->indice + 1 >= vm->c) {
        fprintf(stderr, "[ACC] Dépassement d'indice\n");
        vm->running = 0;
        return;
    }
    // on récupère la valeur non encodée de n
    int n = vm->codes[vm->indice + 1];
    if (vm->p.top < n) {
        fprintf(stderr, "[ACC] Pile de profondeur insuffisante\n");
        vm->running = 0; // on arrête la machine virtuelle en cas d'erreur
        return;
    } else { // si la profondeur de la pile convient alors on peut continuer
        vm->accu = vm->p.data[vm->p.top - n];
    }
    // dans tous les cas on incrémente de 2 indice pour pas rester
    vm->indice += 2;
}

/*  @requires   vm : machine virtuelle valide 
                vm->p une pile non saturée
    @assigns    vm->indice ; vm->running ; vm->p
    @ensures    le contenu de l'accumulateur est empilé
                vm->indice est incrémenté de 1
*/
void PUSH(vim *vm) {
    // on empile la valeur de l'accumulateur
    // mais on vérifie d'abord qu'on ne dépasse pas la taille maximale de la pile
    if (empile(&vm->p, vm->accu) == -1) {
        fprintf(stderr, "[PUSH] Dépassement de la taille maximale de la pile\n");
        vm->running = 0; // on arrête la machine virtuelle en cas d'erreur
        return;
    }
    // on incrémente l'indice de 1 pour passer à l'instruction suivante
    vm->indice++;
}

/*  @requires   vm : machine virtuelle valide 
    @assigns    vm->accu ; vm->indice ; vm->running ; vm->p
    @ensures    le contenu de l'accumulateur est empilé
                vm->accu contient la valeur à la profondeur n de la pile
                vm->indice est incrémenté de 1
*/
void PUSHACCN(vim *vm, int n) {
    PUSH(vm); // indice incrémenté discretement
    vm->indice--; // on remet l'indice à la bonne valeur
    ACCN(vm, n); // indice incrémenté discretement de 1 à la fin 
}

// Application rapide de PUSHACCN avec N = n \in [| 1; 7 |]

/*  @requires   vm : machine virtuelle valide 
    @assigns    vm->accu ; vm->indice ; vm->running ; vm->p
    @ensures    le contenu de l'accumulateur est empilé
                vm->accu contient la valeur à la profondeur 0 de la pile
                vm->indice est incrémenté de 1
*/
void PUSHACC0(vim *vm) { 
    PUSH(vm); // indice incrémenté discretement
    vm->indice--; // on remet l'indice à la bonne valeur
    ACC0(vm); // indice incrémenté discretement de 1 à la fin

}

/*  @requires   vm : machine virtuelle valide 
    @assigns    vm->accu ; vm->indice ; vm->running
    @ensures    le contenu de l'accumulateur est empilé
                vm->accu contient la valeur à la profondeur 1 de la pile
                vm->indice est incrémenté de 1
*/
void PUSHACC1(vim *vm) {
    PUSHACCN(vm, 1);
}

/*  @requires   vm : machine virtuelle valide 
    @assigns    vm->accu ; vm->indice ; vm->running
    @ensures    le contenu de l'accumulateur est empilé
                vm->accu contient la valeur à la profondeur 2 de la pile
                vm->indice est incrémenté de 1
*/
void PUSHACC2(vim *vm) {
    PUSHACCN(vm, 2);
}

/*  @requires   vm : machine virtuelle valide 
    @assigns    vm->accu ; vm->indice ; vm->running
    @ensures    le contenu de l'accumulateur est empilé
                vm->accu contient la valeur à la profondeur 3 de la pile
                vm->indice est incrémenté de 1
*/
void PUSHACC3(vim *vm) {
    PUSHACCN(vm, 3);
}

/*  @requires   vm : machine virtuelle valide 
    @assigns    vm->accu ; vm->indice ; vm->running
    @ensures    le contenu de l'accumulateur est empilé
                vm->accu contient la valeur à la profondeur 4 de la pile
                vm->indice est incrémenté de 1
*/
void PUSHACC4(vim *vm) {
    PUSHACCN(vm, 4);
}

/*  @requires   vm : machine virtuelle valide 
    @assigns    vm->accu ; vm->indice ; vm->running
    @ensures    le contenu de l'accumulateur est empilé
                vm->accu contient la valeur à la profondeur 5 de la pile
                vm->indice est incrémenté de 1
*/
void PUSHACC5(vim *vm) {
    PUSHACCN(vm, 5);
}

/*  @requires   vm : machine virtuelle valide 
    @assigns    vm->accu ; vm->indice ; vm->running
    @ensures    le contenu de l'accumulateur est empilé
                vm->accu contient la valeur à la profondeur 6 de la pile
                vm->indice est incrémenté de 1
*/
void PUSHACC6(vim *vm) {
    PUSHACCN(vm, 6);
}

/*  @requires   vm : machine virtuelle valide 
    @assigns    vm->accu ; vm->indice ; vm->running
    @ensures    le contenu de l'accumulateur est empilé
                vm->accu contient la valeur à la profondeur 7 de la pile
                vm->indice est incrémenté de 1
*/
void PUSHACC7(vim *vm) {
    PUSHACCN(vm, 7);
}


/*  @requires   vm : machine virtuelle valide 
                vm->p une pile de profondeur minimale n - 1 avec n la valeur suivante du tableau de code
    @assigns    vm->accu ; vm->indice ; vm->running ; vm->p
    @ensures    le contenu de l'accumulateur est empilé
                vm->accu contient la valeur à la profondeur n de la pile
                vm->indice est incrémenté de 2
*/
void PUSHACC(vim *vm) {
    // on vérifie qu'il n'y a pas de dépassement
    // vm->indice ne peut pas être négatif car il est du type unsigned int 
    if (vm->indice + 1 >= vm->c) {
        fprintf(stderr, "[PUSHACC] Dépassement d'indice\n");
        vm->running = 0;
        return;
    }
    // on récupère la valeur non encodée de n
    int n = vm->codes[vm->indice + 1];
    PUSH(vm); // indice discrétement incrémentée de 1
    vm->indice--; // donc on le remet à la bonne valeur
    if (vm->p.top < n) {
        fprintf(stderr, "[PUSHACC] Pile de profondeur insuffisante\n");
        // on arrête la machine virtuelle en cas d'erreur
        vm->running = 0;
        return;
    } else {
        vm->accu = vm->p.data[vm->p.top - n];
    }
    // On incrémente de 2 l'indice à la fin pour passer à l'instruction suivante 
    vm->indice += 2;
}

/*  @requires   vm : machine virtuelle valide 
    @assigns    vm->p ; vm->indice ; vm->running
    @ensures    on retire les n éléments les moins profonds de la pile avec n la valeur suivante du tableau de code
                vm->indice est incrémenté de 2
*/
void POP(vim *vm) {
    // on vérifie qu'il n'y a pas de dépassement
    // vm->indice ne peut pas être négatif car il est du type unsigned int 
    if (vm->indice + 1 >= vm->c) {
        fprintf(stderr, "[POP] Dépassement d'indice\n");
        vm->running = 0;
        return;
    }
    // on récupère la valeur non encodée de n
    int n = vm->codes[vm->indice + 1];
    // on dépile n éléments
    int err;
    for (int i = 0; i < n; i++) {
        depile(&vm->p, &err);
        if (err) {
            fprintf(stderr, "[POP] Pile de profondeur insuffisante.\n");
            vm->running = 0;
            return;
        }
    }
    // on incrémente l'indice de 2
    vm->indice += 2;
}

/*  @requires   vm : machine virtuelle valide 
    @assigns    vm->p ; vm->indice ; vm->running ; vm->accu
    @ensures    On remplace la valeur située dans la pile à la profondeur n par celle dans l'accumulateur avec n la valeur suivante du tableau de code
                vm->indice est incrémenté de 2
                vm->accu prend la valeur 1
*/
void ASSIGN(vim *vm) {
    // on vérifie qu'il n'y a pas de dépassement
    // vm->indice ne peut pas être négatif car il est du type unsigned int 
    if (vm->indice + 1 >= vm->c) {
        fprintf(stderr, "[ASSIGN] Dépassement d'indice\n");
        vm->running = 0;
        return;
    }
    // on récupère la valeur non encodée de n
    int n = vm->codes[vm->indice + 1];
    if (vm->p.top < n) {
        fprintf(stderr, "[ASSIGN] Pile de profondeur insuffisante\n");
        vm->running = 0; // on arrête la machine virtuelle en cas d'erreur
        return;
    } else {
        // on remplace la valeur située dans la pile à la profondeur n par celle dans l'accumulateur
        vm->p.data[vm->p.top - n] = vm->accu;
        // on place 1 dans l'accumulateur
        vm->accu = 1;
    }
    // on incrémente l'indice de 2
    vm->indice += 2;
}

/*  @requires   vm : machine virtuelle valide 
    @assigns    vm->running
    @ensures    vm->running prend la valeur 0
*/
void STOP(vim *vm) {
    vm->running = 0;
    // pas besoin d'incrémenter l'indice puisque la machine s'arrête
    // pas besoin non plus de toucher à l'accumulateur ou le retourner
    // la valeur finale de l'accumulateur est déjà sauvegardée dans la structure
}

/*  @requires   vm : machine virtuelle valide 
    @assigns    vm->indice
    @ensures    vm->indice est incrémenté de 1
*/
void CHECK_SIGNALS(vim *vm) {
    // Cette fonction ne fait rien dans cette version de la machine virtuelle
    // mais on incrémente l'indice de 1 pour passer à l'instruction suivante
    vm->indice++;
}



////////////////////////////// Branchements ////////////////////////////////////



/*  @requires   vm : machine virtuelle valide 
    @assigns    vm->indice ; vm->running
    @ensures    vm->indice est incrémenté de n+1 avec n la valeur suivante du tableau de code
*/
void BRANCH(vim *vm){
    // on vérifie qu'il n'y a pas de dépassement
    // vm->indice ne peut pas être négatif car il est du type unsigned int 
    if (vm->indice + 1 >= vm->c) {
        fprintf(stderr, "[BRANCH] Dépassement d'indice\n");
        vm->running = 0;
        return;
    }
    // on récupère la valeur non encodée de n
    int n = vm->codes[vm->indice + 1];
    // on avance l'indice de n+1
    vm->indice += n + 1;
}

/*  @requires   vm : machine virtuelle valide 
    @assigns    vm->indice ; vm->running
    @ensures    vm->indice est incrémenté de n+1 ou 2 avec n la valeur suivante du tableau de code respectivement si la valeur dans l'accumulateur n'est pas l'encodage de false ou non 
*/
void BRANCHIF(vim *vm) {
    // on vérifie qu'il n'y a pas de dépassement
    // vm->indice ne peut pas être négatif car il est du type unsigned int 
    if (vm->indice + 1 >= vm->c) {
        fprintf(stderr, "[BRANCHIF] Dépassement d'indice\n");
        vm->running = 0;
        return;
    }
    // on récupère la valeur non encodée de n
    int n = vm->codes[vm->indice + 1];
    if (vm->accu != encode(false)) {
        // on avance l'indice de n+1
        vm->indice += n + 1;
    } else {
        // sinon on l'avance de 2
        vm->indice += 2;
    }
}


/*  @requires   vm : machine virtuelle valide 
    @assigns    vm->indice ; vm->running
    @ensures    vm->indice est incrémenté de n+1 ou 2 avec n la valeur suivante du tableau de code respectivement si la valeur dans l'accumulateur est l'encodage de false ou non 
*/
void BRANCHIFNOT(vim *vm){
    // on vérifie qu'il n'y a pas de dépassement
    // vm->indice ne peut pas être négatif car il est du type unsigned int 
    if (vm->indice + 1 >= vm->c) {
        fprintf(stderr, "[BRANCHIFNOT] Dépassement d'indice\n");
        vm->running = 0;
        return;
    }
    // on récupère la valeur encodée de n
    int n = vm->codes[vm->indice + 1];
    if (vm->accu == encode(false)) {
        // on avance l'indice de n+1
        vm->indice += n + 1;
    } else {
        // sinon on l'avance de 2
        vm->indice += 2;
    }
}

/*  @requires   vm : machine virtuelle valide 
    @assigns    vm->indice ; vm->running
    @ensures    vm->indice est incrémenté de ci + 2 avec i la valeur décodée de l'accumulateur et ci la valeur décodée située à l'indice n + i + 2 du tableau de codes, n étant la valeur encodée suivante du tableau de codes
*/
void SWITCH(vim *vm){
    // on vérifie qu'il n'y a pas de dépassement
    // vm->indice ne peut pas être négatif car il est du type unsigned int 
    if (vm->indice + 1 >= vm->c) {
        fprintf(stderr, "[SWITCH] Dépassement d'indice\n");
        vm->running = 0;
        return;
    }
    // on récupère la valeur non encodée de n
    int n = vm->codes[vm->indice + 1];
    // on décode la valeur de l'accumulateur
    int i = decode(vm->accu);
    // on vérifie que i est bien dans les limites
    if (i < 0 || i >= n) {
        fprintf(stderr, "[SWITCH] Indice i hors limites\n");
        vm->running = 0;
        return;
    }
    // on vérifie qu'on ne dépasse pas les limites du tableau de codes
    if (vm->indice + i + 2 >= vm->c) {
        fprintf(stderr, "[SWITCH] Dépassement d'indice\n");
        vm->running = 0;
        return;
    }
    int c_i = vm->codes[vm->indice + i + 2];
    // on avance l'indice de ci + 2
    vm->indice += c_i + 2;
}
    
/*  @requires   vm : machine virtuelle valide 
                l'accumulateur contient l'encodage d'un booléen.
    @assigns    vm->indice ; vm->running ; vm->accu
    @ensures    vm->accu prend la valeur de l'encodage de la négation de son ancienne valeur. 
                vm->indice est incrémenté de 1 
*/
void BOOLNOT(vim *vm){
    // si l'accumulateur contient la valeur encodée d'un booléen on la remplace par sa négation encodée
    if (vm->accu == encode(true)) {
        vm->accu = encode(false);
    } else if (vm->accu == encode(false)) {
        vm->accu = encode(true);
    } else { 
        // sinon on renvoie une erreur
        fprintf(stderr, "[BOOLNOT] la valeur de l'accumulateur n'est pas un booléen\n");
        vm->running = 0;
        return;
    }
    // on incrémente l'indice de 1 pour passer à l'instruction suivante
    vm->indice++;
}

/*  @requires   vm : machine virtuelle valide 
                vm->p doit être une pile non vide
    @assigns    vm->indice ; vm->running ; vm->p ; vm->accu
    @ensures    vm->p est dépilée une fois
                vm->accu prend la valeur de l'encodage de la true ou false respectivement si la valeur contenue dans l'accumulateur et celle dépilée sont égales ou non 
                vm->indice est incrémenté de 1 
*/
void EQ(vim *vm){
    int err;
    long n = depile(&vm->p, &err);
    if (err) {
        fprintf(stderr, "[EQ] Pile vide, on ne peut pas dépiler.\n");
        vm->running = 0;
        return;
    }
    // Pourquoi les valeurs encodées ne peuvent pas être comparés ? la fonction d'encodage est bien injective pourtant
    if (decode(n) == decode(vm->accu)) {
    //if (n == vm->accu) {
        vm->accu = encode(true);
    } else {
        vm->accu = encode(false);
    }
    // on incrémente l'indice de 1 pour passer à l'instruction suivante
    vm->indice++;
}


/*  @requires   vm : machine virtuelle valide 
                vm->p doit être une pile non vide
    @assigns    vm->indice ; vm->running ; vm->p ; vm->accu
    @ensures    vm->p est dépilée une fois
                vm->accu prend la valeur de l'encodage de la true ou false respectivement si la valeur contenue dans l'accumulateur et celle dépilée ne sont pas égales ou le sont
                vm->indice est incrémenté de 1 
*/
void NEQ(vim *vm){
    int err;
    long n = depile(&vm->p, &err);
    if (err) {
        fprintf(stderr, "[NEQ] Pile vide, on ne peut pas dépiler.\n");
        vm->running = 0;
        return;
    }
    // Pourquoi les valeurs encodées ne peuvent pas être comparés ? la fonction d'encodage est bien injective pourtant
    if (decode(n) == decode(vm->accu)) {
    //if (n == vm->accu) {
        vm->accu = encode(false);
    } else {
        vm->accu = encode(true);
    }
    // on incrémente l'indice de 1 pour passer à l'instruction suivante
    vm->indice++;
}



////////////////////////////////// Entiers //////////////////////////////////////



/*  @requires   vm : machine virtuelle valide 
    @assigns    vm->indice ; vm->accu
    @ensures    vm->accu prend la valeur de l'encodage de n
                vm->indice est incrémenté de 1 
*/
void CONSTN(vim *vm, int n) {
    // on met dans l'accumulateur la valeur encodée de n
    vm->accu = encode(n);
    // on incrémente l'indice de 1 pour passer à l'instruction suivante
    vm->indice++;
}

// application directe de CONSTN pour n de 0 à 3


/*  @requires   vm : machine virtuelle valide 
    @assigns    vm->indice ; vm->accu
    @ensures    vm->accu prend la valeur de l'encodage de 0
                vm->indice est incrémenté de 1 
*/
void CONST0(vim *vm) {
    CONSTN(vm, 0);
}

/*  @requires   vm : machine virtuelle valide 
    @assigns    vm->indice ; vm->accu
    @ensures    vm->accu prend la valeur de l'encodage de 1
                vm->indice est incrémenté de 1
*/
void CONST1(vim *vm) {
    CONSTN(vm, 1);
}

/*  @requires   vm : machine virtuelle valide 
    @assigns    vm->indice ; vm->accu
    @ensures    vm->accu prend la valeur de l'encodage de 2
                vm->indice est incrémenté de 1 
*/
void CONST2(vim *vm) {
    CONSTN(vm, 2);
}

/*  @requires   vm : machine virtuelle valide 
    @assigns    vm->indice ; vm->accu
    @ensures    vm->accu prend la valeur de l'encodage de 3
                vm->indice est incrémenté de 1 
*/
void CONST3(vim *vm) {
    CONSTN(vm, 3);
}

/*  @requires   vm : machine virtuelle valide 
    @assigns    vm->indice ; vm->running ; vm->accu
    @ensures    vm->accu prend la valeur de l'encodage de n avec n la valeur suivante du tableau de code
                vm->indice est incrémenté de 2
*/
void CONSTINT(vim *vm){
    // on vérifie qu'il n'y a pas de dépassement
    // vm->indice ne peut pas être négatif car il est du type unsigned int 
    if (vm->indice + 1 >= vm->c) {
        fprintf(stderr, "[CONSTINT] Dépassement d'indice\n");
        vm->running = 0;
        return;
    }
    // on récupère la valeur non encodée de n
    int n = vm->codes[vm->indice + 1];
    // on met la valeur encodée de n dans l'accumulateur
    vm->accu = encode(n);
    // on avance l'indice de 2 pour aller à la prochaine instruction
    vm->indice += 2;
}

/*  @requires   vm : machine virtuelle valide
                vm->p non saturée
    @assigns    vm->indice ; vm->running ; vm->accu ; vm->p 
    @ensures    le contenu de l'accumulateur est empilé
                vm->accu prend la valeur de l'encodage de 0
                vm->indice est incrémenté de 1
*/
void PUSHCONST0(vim *vm) {
    PUSH(vm); // indice incrémenté de 1 discrètement 
    vm->indice--; // on le remet à la bonne valeur
    CONST0(vm); // indice incrémenté de 1 discrètement 
    // au final l'indice est incrémenté de 1 pour passer à l'instruction suivante seulement à la fin
    
}

/*  @requires   vm : machine virtuelle valide
                vm->p non saturée
    @assigns    vm->indice ; vm->running ; vm->accu ; vm->p 
    @ensures    le contenu de l'accumulateur est empilé
                vm->accu prend la valeur de l'encodage de 1
                vm->indice est incrémenté de 1
*/
void PUSHCONST1(vim *vm) {
    PUSH(vm); // indice incrémenté de 1 discrètement 
    vm->indice--; // on le remet à la bonne valeur
    CONST1(vm); // indice incrémenté de 1 discrètement 
    // au final l'indice est incrémenté de 1 pour passer à l'instruction suivante seulement à la fin
    
}

/*  @requires   vm : machine virtuelle valide
                vm->p non saturée
    @assigns    vm->indice ; vm->running ; vm->accu ; vm->p 
    @ensures    le contenu de l'accumulateur est empilé
                vm->accu prend la valeur de l'encodage de 2
                vm->indice est incrémenté de 1
*/
void PUSHCONST2(vim *vm) {
    PUSH(vm); // indice incrémenté de 1 discrètement
    vm->indice--; // on le remet à la bonne valeur
    CONST2(vm); // indice incrémenté de 1 discrètement
    // au final l'indice est incrémenté de 1 pour passer à l'instruction suivante seulement à la fin

}

/*  @requires   vm : machine virtuelle valide
                vm->p non saturée
    @assigns    vm->indice ; vm->running ; vm->accu ; vm->p 
    @ensures    le contenu de l'accumulateur est empilé
                vm->accu prend la valeur de l'encodage de 3
                vm->indice est incrémenté de 1
*/
void PUSHCONST3(vim *vm) {
    PUSH(vm); // indice incrémenté de 1 discrètement
    vm->indice--; // on le remet à la bonne valeur
    CONST3(vm); // indice incrémenté de 1 discrètement
    // au final l'indice est incrémenté de 1 pour passer à l'instruction suivante seulement à la fin

}

/*  @requires   vm : machine virtuelle valide
                vm->p non saturée
    @assigns    vm->indice ; vm->running ; vm->accu ; vm->p 
    @ensures    le contenu de l'accumulateur est empilé
                vm->accu prend la valeur de l'encodage de n avec n la valeur suivante du tableau de code
                vm->indice est incrémenté de 2
*/
void PUSHCONSTINT(vim *vm) {
    PUSH(vm); // indice incrémenté de 1 discrètement
    vm->indice--; // on le remet à la bonne valeur
    CONSTINT(vm); // incrémente de 2
    // au final l'indice est incrémenté de 2 pour passer à l'instruction suivante seulement à la fin
}

/*  @requires   vm : machine virtuelle valide
    @assigns    vm->indice ; vm->accu 
    @ensures    vm->accu prend la valeur de l'encodage de -n avec n la valeur de l'accumulateur au début de l'exécution de NEGINT
                vm->indice est incrémenté de 1
*/
void NEGINT(vim *vm) {
    // L'accumulateur qui contenait l'encodage de l'entier n prend maintenant la valeur décodée de -n.
    vm->accu = -1 * decode(vm->accu);
    // puis on reencore -n 
    vm->accu = encode(vm->accu);
    // incrémentation de l'indice pour aller à la prochaine instruction
    vm->indice++;
}

/*  @requires   vm : machine virtuelle valide
                vm->p doit être une pile non vide
    @assigns    vm->indice ; vm->accu ; vm->p ; vm->running
    @ensures    vm->accu prend la valeur de l'encodage de m+n avec n la valeur de l'accumulateur au début de l'exécution de ADDINT et m la valeur qu'on dépile de vm->p
                vm->indice est incrémenté de 1
*/
void ADDINT(vim *vm){
    long n = decode(vm->accu);
    int err;
    long m = depile(&vm->p, &err);
    if (err) {
        fprintf(stderr, "[ADDINT] Pile vide, on ne peut pas dépiler.\n");
        vm->running = 0;
        return;
    }
    m = decode(m);
    // l'accumulateur prend la valeur de (n + m) encodée
    vm->accu = encode(n + m);
    // incrémentation de l'indice pour aller à la prochaine instruction
    vm->indice++;
}

/*  @requires   vm : machine virtuelle valide
                vm->p doit être une pile non vide
    @assigns    vm->indice ; vm->accu ; vm->p ; vm->running
    @ensures    vm->accu prend la valeur de l'encodage de m-n avec n la valeur de l'accumulateur au début de l'exécution de SUBINT et m la valeur qu'on dépile de vm->p
                vm->indice est incrémenté de 1
*/
void SUBINT(vim *vm){
    long n = decode(vm->accu);
    int err;
    long m = depile(&vm->p, &err);
    if (err) {
        fprintf(stderr, "[SUBINT] Pile vide, on ne peut pas dépiler.\n");
        vm->running = 0;
        return;
    }
    m = decode(m);
    // l'accumulateur prend la valeur de (n - m) encodée
    vm->accu = encode(n - m);
    // incrémentation de l'indice pour aller à la prochaine instruction
    vm->indice++;
}

/*  @requires   vm : machine virtuelle valide
                vm->p doit être une pile non vide
    @assigns    vm->indice ; vm->accu ; vm->p ; vm->running
    @ensures    vm->accu prend la valeur de l'encodage de m*n avec n la valeur de l'accumulateur au début de l'exécution de MULINT et m la valeur qu'on dépile de vm->p
                vm->indice est incrémenté de 1
*/
void MULINT(vim *vm){
    long n = decode(vm->accu);
    int err;
    long m = depile(&vm->p, &err);
    if (err) {
        fprintf(stderr, "[MULINT] Pile vide, on ne peut pas dépiler.\n");
        vm->running = 0;
        return;
    }
    m = decode(m);
    // l'accumulateur prend la valeur de (n * m) encodée
    vm->accu = encode(n * m);
    // incrémentation de l'indice pour aller à la prochaine instruction
    vm->indice++;
}

/*  @requires   vm : machine virtuelle valide
                vm->p doit être une pile non vide
    @assigns    vm->indice ; vm->accu ; vm->p ; vm->running
    @ensures    vm->accu prend la valeur de l'encodage de n/m si m!= 0 avec n la valeur de l'accumulateur au début de l'exécution de DIVINT et m la valeur qu'on dépile de vm->p 
                vm->indice est incrémenté de 1
*/
void DIVINT(vim *vm){
    long n = decode(vm->accu);
    int err;
    long m = depile(&vm->p, &err);
    if (err) {
        fprintf(stderr, "[DINVINT] Pile vide, on ne peut pas dépiler.\n");
        vm->running = 0;
        return;
    }
    m = decode(m);
    if (m == 0) {
        fprintf(stderr, "Fatal error: exception Division_by_zero\n");
        // on quitte avec le code d'erreur 2
        vm->running = 0;
        return;
    } // si la division est possible alors
    // l'accumulateur prend la valeur de (n / m) encodée
    vm->accu = encode(n / m);
    // incrémentation de l'indice pour aller à la prochaine instruction
    vm->indice++;
}

/*  @requires   vm : machine virtuelle valide
                vm->p doit être une pile non vide
    @assigns    vm->indice ; vm->accu ; vm->p ; vm->running
    @ensures    vm->accu prend la valeur de l'encodage de n%m si m!= 0 avec n la valeur de l'accumulateur au début de l'exécution de MODINT et m la valeur qu'on dépile de vm->p 
                vm->indice est incrémenté de 1
*/
void MODINT(vim *vm){
    long n = decode(vm->accu);
    int err;
    long m = depile(&vm->p, &err);
    if (err) {
        fprintf(stderr, "[MODINT] Pile vide, on ne peut pas dépiler.\n");
        vm->running = 0;
        return;
    }
    m = decode(m);
    if (m == 0) {
        fprintf(stderr, "Fatal error: exception Division_by_zero\n");
        // on quitte avec le code d'erreur 2
        vm->running = 0;
        return;
    } // si le modulo est possible alors
    // l'accumulateur prend la valeur de (n % m) encodée
    vm->accu = encode(n % m);
    // incrémentation de l'indice pour aller à la prochaine instruction
    vm->indice++;
}

/*  @requires   vm : machine virtuelle valide
                vm->p doit être une pile non vide
    @assigns    vm->indice ; vm->accu ; vm->p ; vm->running
    @ensures    vm->accu prend la valeur de l'encodage de m & n avec n la valeur de l'accumulateur au début de l'exécution de ANDINT et m la valeur qu'on dépile de vm->p
                vm->indice est incrémenté de 1
*/
void ANDINT(vim *vm){
    long n = decode(vm->accu);
    int err;
    long m = depile(&vm->p, &err);
    if (err) {
        fprintf(stderr, "[ANDINT] Pile vide, on ne peut pas dépiler.\n");
        vm->running = 0;
        return;
    }
    m = decode(m);
    // l'accumulateur prend la valeur de (n & m)  : (et bit à bit) encodée  
    vm->accu = encode(n & m);
    // incrémentation de l'indice pour aller à la prochaine instruction
    vm->indice++;
}


/*  @requires   vm : machine virtuelle valide
                vm->p doit être une pile non vide
    @assigns    vm->indice ; vm->accu ; vm->p ; vm->running
    @ensures    vm->accu prend la valeur de l'encodage de m & n avec n la valeur de l'accumulateur au début de l'exécution de ORINT et m la valeur qu'on dépile de vm->p
                vm->indice est incrémenté de 1
*/
void ORINT(vim *vm){
    long n = decode(vm->accu);
    int err;
    long m = depile(&vm->p, &err);
    if (err) {
        fprintf(stderr, "[ORINT] Pile vide, on ne peut pas dépiler.\n");
        vm->running = 0;
        return;
    }
    m = decode(m);
    // l'accumulateur prend la valeur de (n | m)  : (ou bit à bit) encodée  
    vm->accu = encode(n | m);
    // incrémentation de l'indice pour aller à la prochaine instruction
    vm->indice++;
}

/*  @requires   vm : machine virtuelle valide
                vm->p doit être une pile non vide
    @assigns    vm->indice ; vm->accu ; vm->p ; vm->running
    @ensures    vm->accu prend la valeur de l'encodage de m ^ n avec n la valeur de l'accumulateur au début de l'exécution de XORINT et m la valeur qu'on dépile de vm->p
                vm->indice est incrémenté de 1
*/
void XORINT(vim *vm){
    long n = decode(vm->accu);
    int err;
    long m = depile(&vm->p, &err);
    if (err) {
        fprintf(stderr, "[XORINT] Pile vide, on ne peut pas dépiler.\n");
        vm->running = 0;
        return;
    }
    m = decode(m);
    // l'accumulateur prend la valeur de (n ^ m)  : (xor bit à bit) encodée  
    vm->accu = encode(n ^ m);
    // incrémentation de l'indice pour aller à la prochaine instruction
    vm->indice++;
}

/*  @requires   vm : machine virtuelle valide
                vm->p doit être une pile non vide
    @assigns    vm->indice ; vm->accu ; vm->p ; vm->running
    @ensures    vm->accu prend la valeur de l'encodage de m >> n avec n la valeur de l'accumulateur au début de l'exécution de LSLINT et m la valeur qu'on dépile de vm->p
                vm->indice est incrémenté de 1
*/
void LSLINT(vim *vm){
    long n = decode(vm->accu);
    int err;
    long m = depile(&vm->p, &err);
    if (err) {
        fprintf(stderr, "[LSLINT] Pile vide, on ne peut pas dépiler.\n");
        vm->running = 0;
        return;
    }
    m = decode(m);
    // l'accumulateur prend la valeur de (n << m)  : (décalage à gauche) encodée  
    vm->accu = encode(n << m);
    // incrémentation de l'indice pour aller à la prochaine instruction
    vm->indice++;
}

/*  @requires   vm : machine virtuelle valide
                vm->p doit être une pile non vide
    @assigns    vm->indice ; vm->accu ; vm->p ; vm->running
    @ensures    vm->accu prend la valeur de l'encodage de m << n avec n la valeur de l'accumulateur au début de l'exécution de LSRINT et m la valeur qu'on dépile de vm->p
                vm->indice est incrémenté de 1
*/
void LSRINT(vim *vm){
    unsigned long n = (unsigned long) decode(vm->accu);
    int err;
    long m = depile(&vm->p, &err);
    if (err) {
        fprintf(stderr, "[LSRINT] Pile vide, on ne peut pas dépiler.\n");
        vm->running = 0;
        return;
    }
    m = decode(m);
    // l'accumulateur prend la valeur de (n >> m)  : (décalage à droite) encodée  
    vm->accu = encode(n >> m);
    // incrémentation de l'indice pour aller à la prochaine instruction
    vm->indice++;
}

/*  @requires   vm : machine virtuelle valide
                vm->p doit être une pile non vide
    @assigns    vm->indice ; vm->accu ; vm->p ; vm->running
    @ensures    vm->accu prend la valeur de l'encodage de m << n avec n la valeur de l'accumulateur au début de l'exécution de ASRINT et m la valeur qu'on dépile de vm->p
                on préserve le signe de n
                vm->indice est incrémenté de 1
*/
void ASRINT(vim *vm){
    long n = decode(vm->accu);
    int err;
    long m = depile(&vm->p, &err);
    if (err) {
        fprintf(stderr, "[ASRINT] Pile vide, on ne peut pas dépiler.\n");
        vm->running = 0;
        return;
    }
    m = decode(m);
    // l'accumulateur prend la valeur de (n >> m)  : (décalage à droite) encodée  
    vm->accu = encode(n >> m);
    // incrémentation de l'indice pour aller à la prochaine instruction
    vm->indice++;
}

/*  @requires   vm : machine virtuelle valide
                vm->p doit être une pile non vide
    @assigns    vm->indice ; vm->accu ; vm->p ; vm->running
    @ensures    vm->accu prend la valeur de l'encodage du booléen qui dit si n est strictement plus petit que m avec n la valeur de l'accumulateur au début de l'exécution de LTINT et m la valeur qu'on dépile de vm->p
                vm->indice est incrémenté de 1
*/
void LTINT(vim *vm){
    long n = decode(vm->accu);
    int err;
    long m = depile(&vm->p, &err);
    if (err) {
        fprintf(stderr, "[LTINT] Pile vide, on ne peut pas dépiler.\n");
        vm->running = 0;
        return;
    }
    m = decode(m);
    // l'accumulateur prend la valeur du booléen de (n < m) : (comparaison) encodée  
    vm->accu = encode(n < m ? true : false);
    // incrémentation de l'indice pour aller à la prochaine instruction
    vm->indice++;
}

/*  @requires   vm : machine virtuelle valide
                vm->p doit être une pile non vide
    @assigns    vm->indice ; vm->accu ; vm->p ; vm->running
    @ensures    vm->accu prend la valeur de l'encodage du booléen qui dit si n est plus petit ou égal que m avec n la valeur de l'accumulateur au début de l'exécution de LEINT et m la valeur qu'on dépile de vm->p
                vm->indice est incrémenté de 1
*/
void LEINT(vim *vm){
    long n = decode(vm->accu);
    int err;
    long m = depile(&vm->p, &err);
    if (err) {
        fprintf(stderr, "[LEINT] Pile vide, on ne peut pas dépiler.\n");
        vm->running = 0;
        return;
    }
    m = decode(m);
    // l'accumulateur prend la valeur du booléen de (n <= m) : (comparaison) encodée  
    vm->accu = encode(n <= m ? true : false);
    // incrémentation de l'indice pour aller à la prochaine instruction
    vm->indice++;
}

/*  @requires   vm : machine virtuelle valide
                vm->p doit être une pile non vide
    @assigns    vm->indice ; vm->accu ; vm->p ; vm->running
    @ensures    vm->accu prend la valeur de l'encodage du booléen qui dit si n est strictement plus grand que m avec n la valeur de l'accumulateur au début de l'exécution de GTINT et m la valeur qu'on dépile de vm->p
                vm->indice est incrémenté de 1
*/
void GTINT(vim *vm){
    long n = decode(vm->accu);
    int err;
    long m = depile(&vm->p, &err);
    if (err) {
        fprintf(stderr, "[GTINT] Pile vide, on ne peut pas dépiler.\n");
        vm->running = 0;
        return;
    }
    m = decode(m);
    // l'accumulateur prend la valeur du booléen de (n > m) : (comparaison) encodée  
    vm->accu = encode(n > m ? true : false);
    // incrémentation de l'indice pour aller à la prochaine instruction
    vm->indice++;
}

/*  @requires   vm : machine virtuelle valide
                vm->p doit être une pile non vide
    @assigns    vm->indice ; vm->accu ; vm->p ; vm->running
    @ensures    vm->accu prend la valeur de l'encodage du booléen qui dit si n est strictement plus grand que m avec n la valeur de l'accumulateur au début de l'exécution de GEINT et m la valeur qu'on dépile de vm->p
                vm->indice est incrémenté de 1
*/
void GEINT(vim *vm){
    int n = decode(vm->accu);
    int err;
    long m = depile(&vm->p, &err);
    if (err) {
        fprintf(stderr, "[GEINT] Pile vide, on ne peut pas dépiler.\n");
        vm->running = 0;
        return;
    }
    m = decode(m);
    // l'accumulateur prend la valeur du booléen de (n >= m) : (comparaison) encodée  
    vm->accu = encode(n >= m ? true : false);
    // incrémentation de l'indice pour aller à la prochaine instruction
    vm->indice++;
}

/*  @requires   vm : machine virtuelle valide
                vm->p doit être une pile non vide
    @assigns    vm->indice ; vm->accu ; vm->p ; vm->running
    @ensures    vm->accu prend la valeur de l'encodage du booléen qui dit si n est strictement plus petit que m (comparaison non signée) avec n la valeur de l'accumulateur au début de l'exécution de ULTINT et m la valeur qu'on dépile de vm->p
                vm->indice est incrémenté de 1
*/
void ULTINT(vim *vm){
    long n = decode(vm->accu);
    int err;
    long m = depile(&vm->p, &err);
    if (err) {
        fprintf(stderr, "[ULTINT] Pile vide, on ne peut pas dépiler.\n");
        vm->running = 0;
        return;
    }
    m = decode(m);
    // l'accumulateur prend la valeur du booléen de (|n| < |m|) : (comparaison) encodée  
    vm->accu = encode(abs_long(n) < abs_long(m) ? true : false);
    // incrémentation de l'indice pour aller à la prochaine instruction
    vm->indice++;
}

/*  @requires   vm : machine virtuelle valide
    @assigns    vm->indice ; vm->accu ; vm->p ; vm->running
    @ensures    vm->accu prend la valeur de l'encodage du booléen qui dit si n est strictement plus grand que m (comparaison non signée) avec n la valeur de l'accumulateur au début de l'exécution de UGEINT et m la valeur qu'on dépile de vm->p
                vm->indice est incrémenté de 1
*/
void UGEINT(vim *vm){
    long n = decode(vm->accu);
    int err;
    long m = depile(&vm->p, &err);
    if (err) {
        fprintf(stderr, "[UGEINT] Pile vide, on ne peut pas dépiler.\n");
        vm->running = 0;
        return;
    }
    m = decode(m);
    // l'accumulateur prend la valeur du booléen de (|n| > |m|) : (comparaison) encodée  
    vm->accu = encode(abs_long(n) > abs_long(m) ? true : false);
    // incrémentation de l'indice pour aller à la prochaine instruction
    vm->indice++;
}

/*  @requires   vm : machine virtuelle valide
    @assigns    vm->indice ; vm->accu ; vm->running
    @ensures    vm->accu prend la valeur de l'encodage de m+n avec n la valeur de l'accumulateur au début de l'exécution de OFFSETINT et m la valeur suivante du tableau de code
                vm->indice est incrémenté de 2
*/
void OFFSETINT(vim *vm){
    long n = decode(vm->accu);
    // on vérifie qu'il n'y a pas de dépassement
    // vm->indice ne peut pas être négatif car il est du type unsigned int 
    if (vm->indice + 1 >= vm->c) {
        fprintf(stderr, "[OFFSETINT] Dépassement d'indice\n");
        vm->running = 0;
        return;
    }
    // on récupère la valeur non encodée de m de type int car elle vient du tableau de code
    int m = vm->codes[vm->indice + 1];
    // l'accumulateur prend la valeur de (n + m) encodée
    vm->accu = encode(n + m);
    // incrémentation de 2 de l'indice pour aller à la prochaine instruction
    vm->indice += 2;
}

/*  @requires   vm : machine virtuelle valide
    @assigns    vm->indice ; vm->accu
    @ensures    vm->accu prend la valeur de l'encodage de true si l'accumulateur actuel contient l'encodage d'un entier donc s'il est impaire, sinon par l'encodage de false. 
                vm->indice est incrémenté de 1
*/
void ISINT(vim *vm){
    long n = vm->accu;
    // l'accumulateur prend la valeur du booléen de (n impair) encodée  
    // impair = pas pair -> fonctionne pour les négatifs
    vm->accu = encode(n % 2 != 0 ? true : false);
    // incrémentation de l'indice pour aller à la prochaine instruction
    vm->indice++;
}

/*  @requires   vm : machine virtuelle valide
    @assigns    vm->indice ; vm->running
    @ensures   Si m = n avec n la valeur de l'accumulateur au début de l'exécution de BEQ, m la valeur encodée suivante du tableau de code et c celle d'encore après décodée  
    alors vm->indice est incrémenté de c + 2
    sinon vm->indice est incrémenté de 3
*/
void BEQ(vim *vm){
    long n = decode(vm->accu);
    // on vérifie qu'il n'y a pas de dépassement
    // vm->indice ne peut pas être négatif car il est du type unsigned int 
    if (vm->indice + 2 >= vm->c) {
        fprintf(stderr, "[BEQ] Dépassement d'indice\n");
        vm->running = 0;
        return;
    }
    // on récupère la valeur non encodée de c
    int c = vm->codes[vm->indice + 2];
    // on récupère la valeur non encodée de m
    int m = vm->codes[vm->indice + 1];
    // si m == n alors on fait le saut
    if (m == n) {
        vm->indice += c + 2;
        return;
    } // sinon on passe à l'instruction suivante
    // incrémentation de 3 de l'indice pour aller à la prochaine instruction
    vm->indice += 3;
}

/*  @requires   vm : machine virtuelle valide
    @assigns    vm->indice ; vm->running
    @ensures   Si m != n avec n la valeur de l'accumulateur au début de l'exécution de BNEQ, m la valeur encodée suivante du tableau de code et c celle d'encore après décodée 
    alors vm->indice est incrémenté de c + 2
    sinon vm->indice est incrémenté de 3
*/
void BNEQ(vim *vm){
    long n = decode(vm->accu);
    // on vérifie qu'il n'y a pas de dépassement
    // vm->indice ne peut pas être négatif car il est du type unsigned int 
    if (vm->indice + 2 >= vm->c) {
        fprintf(stderr, "[BNEQ] Dépassement d'indice\n");
        vm->running = 0;
        return;
    }
    // on récupère la valeur non encodée de c
    int c = vm->codes[vm->indice + 2];
    // on récupère la valeur non encodée de m
    int m = vm->codes[vm->indice + 1];
    // si m != n alors on fait le saut
    if (m != n) {
        vm->indice += c + 2;
        return;
    } // sinon on passe à l'instruction suivante
    // incrémentation de 3 de l'indice pour aller à la prochaine instruction
    vm->indice += 3;
}

/*  @requires   vm : machine virtuelle valide
    @assigns    vm->indice ; vm->running
    @ensures   Si m < n avec n la valeur de l'accumulateur au début de l'exécution de BLTINT, m la valeur encodée suivante du tableau de code et c celle d'encore après décodée 
    alors vm->indice est incrémenté de c + 2
    sinon vm->indice est incrémenté de 3
*/
void BLTINT(vim *vm){
    long n = decode(vm->accu);
    // on vérifie qu'il n'y a pas de dépassement
    // vm->indice ne peut pas être négatif car il est du type unsigned int 
    if (vm->indice + 2 >= vm->c) {
        fprintf(stderr, "[BLTINT] Dépassement d'indice\n");
        vm->running = 0;
        return;
    }
    // on récupère la valeur non encodée de c
    int c = vm->codes[vm->indice + 2];
    // on récupère la valeur non encodée de m
    int m = vm->codes[vm->indice + 1];
    // si m < n alors on fait le saut
    if (m < n) {
        vm->indice += c + 2;
        return;
    } // sinon on passe à l'instruction suivante
    // incrémentation de 3 de l'indice pour aller à la prochaine instruction
    vm->indice += 3;
}

/*  @requires   vm : machine virtuelle valide
    @assigns    vm->indice ; vm->running
    @ensures   Si m <= n avec n la valeur de l'accumulateur au début de l'exécution de BLEINT, m la valeur encodée suivante du tableau de code et c celle d'encore après décodée 
    alors vm->indice est incrémenté de c + 2
    sinon vm->indice est incrémenté de 3
*/
void BLEINT(vim *vm){
    long n = decode(vm->accu);
    // on vérifie qu'il n'y a pas de dépassement
    // vm->indice ne peut pas être négatif car il est du type unsigned int 
    if (vm->indice + 2 >= vm->c) {
        fprintf(stderr, "[BLEINT] Dépassement d'indice\n");
        vm->running = 0;
        return;
    }
    // on récupère la valeur non encodée de c
    int c = vm->codes[vm->indice + 2];
    // on récupère la valeur non encodée de m
    int m = vm->codes[vm->indice + 1];
    // si m <= n alors on fait le saut
    if (m <= n) {
        vm->indice += c + 2;
        return;
    } // sinon on passe à l'instruction suivante
    // incrémentation de 3 de l'indice pour aller à la prochaine instruction
    vm->indice += 3;
}

/*  @requires   vm : machine virtuelle valide
    @assigns    vm->indice ; vm->running
    @ensures   Si m > n avec n la valeur de l'accumulateur au début de l'exécution de BGTINT, m la valeur encodée suivante du tableau de code et c celle d'encore après décodée 
    alors vm->indice est incrémenté de c + 2
    sinon vm->indice est incrémenté de 3
*/
void BGTINT(vim *vm){
    long n = decode(vm->accu);
    // on vérifie qu'il n'y a pas de dépassement
    // vm->indice ne peut pas être négatif car il est du type unsigned int 
    if (vm->indice + 2 >= vm->c) {
        fprintf(stderr, "[BGTINT] Dépassement d'indice\n");
        vm->running = 0;
        return;
    }
    // on récupère la valeur non encodée de c
    int c = vm->codes[vm->indice + 2];
    // on récupère la valeur non encodée de m
    int m = vm->codes[vm->indice + 1];
    // si m > n alors on fait le saut
    if (m > n) {
        vm->indice += c + 2;
        return;
    } // sinon on passe à l'instruction suivante
    // incrémentation de 3 de l'indice pour aller à la prochaine instruction
    vm->indice += 3;
}

/*  @requires   vm : machine virtuelle valide
    @assigns    vm->indice ; vm->running
    @ensures   Si m >= n avec n la valeur de l'accumulateur au début de l'exécution de BGEINT, m la valeur encodée suivante du tableau de code et c celle d'encore après décodée 
    alors vm->indice est incrémenté de c + 2
    sinon vm->indice est incrémenté de 3
*/
void BGEINT(vim *vm){
    long n = decode(vm->accu);
    // on vérifie qu'il n'y a pas de dépassement
    // vm->indice ne peut pas être négatif car il est du type unsigned int 
    if (vm->indice + 2 >= vm->c) {
        fprintf(stderr, "[BGEINT] Dépassement d'indice\n");
        vm->running = 0;
        return;
    }
    // on récupère la valeur non encodée de c
    int c = vm->codes[vm->indice + 2];
    // on récupère la valeur non encodée de m
    int m = vm->codes[vm->indice + 1];
    // si m >= n alors on fait le saut
    if (m >= n) {
        vm->indice += c + 2;
        return;
    } // sinon on passe à l'instruction suivante
    // incrémentation de 3 de l'indice pour aller à la prochaine instruction
    vm->indice += 3;
}

/*  @requires   vm : machine virtuelle valide
    @assigns    vm->indice ; vm->running
    @ensures   Si |m| < |n| (comparaison non signée) avec n la valeur de l'accumulateur au début de l'exécution de BULTINT, m la valeur encodée suivante du tableau de code et c celle d'encore après décodée 
    alors vm->indice est incrémenté de c + 2
    sinon vm->indice est incrémenté de 3
*/
void BULTINT(vim *vm){
    long n = decode(vm->accu);
    // on vérifie qu'il n'y a pas de dépassement
    // vm->indice ne peut pas être négatif car il est du type unsigned int 
    if (vm->indice + 2 >= vm->c) {
        fprintf(stderr, "[BULTINT] Dépassement d'indice\n");
        vm->running = 0;
        return;
    }
    // on récupère la valeur non encodée de c
    int c = vm->codes[vm->indice + 2];
    // on récupère la valeur non encodée de m
    int m = vm->codes[vm->indice + 1];
    // si |m| < |n| alors on fait le saut
    if (abs_long(m) < abs_long(n)) {
        vm->indice += c + 2;
        return;
    } // sinon on passe à l'instruction suivante
    // incrémentation de 3 de l'indice pour aller à la prochaine instruction
    vm->indice += 3;
}

/*  @requires   vm : machine virtuelle valide
    @assigns    vm->indice ; vm->running
    @ensures   Si |m| > |n| (comparaison non signée) avec n la valeur de l'accumulateur au début de l'exécution de BUGEINT, m la valeur encodée suivante du tableau de code et c celle d'encore après décodée 
    alors vm->indice est incrémenté de c + 2
    sinon vm->indice est incrémenté de 3
*/
void BUGEINT(vim *vm){
    long n = decode(vm->accu);
    // on vérifie qu'il n'y a pas de dépassement
    // vm->indice ne peut pas être négatif car il est du type unsigned int 
    if (vm->indice + 2 >= vm->c) {
        fprintf(stderr, "[BUGEINT] Dépassement d'indice\n");
        vm->running = 0;
        return;
    }
    // on récupère la valeur non encodée de c
    int c = vm->codes[vm->indice + 2];
    // on récupère la valeur non encodée de m
    int m = vm->codes[vm->indice + 1];
    // si |m| > |n| alors on fait le saut
    if (abs_long(m) > abs_long(n)) {
        vm->indice += c + 2;
        return;
    } // sinon on passe à l'instruction suivante
    // incrémentation de 3 de l'indice pour aller à la prochaine instruction
    vm->indice += 3;
}



///////////////////////////////////// PRIMITIVES /////////////////////////////////////////




/*  @requires   vm : machine virtuelle valide
    @assigns    vm->running
    @ensures    Retourne un tableau d'entiers de taille n dont chaque case vaut v2 avec n et v2 les valeurs des paramètres d'entrée
*/
long* primitive15(vim *vm, long n, long v2) {
    // on décode n pour avoir la taille du tableau
    n = decode(n);
    // on crée le tableau de taille n dont chaque case vaut v2
    long *tab = malloc(n * sizeof(long));
    if (tab == NULL) {
        fprintf(stderr, "[primitive15] Erreur d'allocation mémoire pour le tableau.\n");
        vm->running = 0;
        return NULL;
    }
    for (int i = 0; i < n; i++) {
        tab[i] = v2;
    }
    return tab;
}

/*  @requires   vm : machine virtuelle valide
                file : pointeur vers un fichier ouvert en écriture
    @assigns    vm->running
    @ensures    Effectue un fflush sur le fichier passé en paramètre
                Retourne -1 en cas d'erreur et arrête vm, 1 sinon
*/
int primitive288(vim *vm, FILE* file) {
    // on purge file
    if (fflush(file) == EOF) {
        fprintf(stderr, "[primitive288] Erreur lors du fflush.\n");
        vm->running = 0;
        return -1;
    }
    return 1;
}

/*  @requires   vm : machine virtuelle valide
                file : pointeur vers un fichier ouvert en écriture
    @assigns    vm->running
    @ensures    lit un caractère dans le fichier passé en paramètre
                et retourne l'encodage du code ASCII du caractère lu
                Retourne -1 en cas d'erreur et arrête vm, 1 sinon
*/
int primitive293(vim *vm, FILE* file) {
    int c;
    // on lit un caractère dans le fichier
    if ( (c = fgetc(file)) == EOF) {
        fprintf(stderr, "[primitive293] Erreur lors de la lecture du caractère.\n");
        vm->running = 0;
        return -1;
    }
    return encode(c);
}

/*  @requires   vm : machine virtuelle valide
                file : pointeur vers un fichier ouvert en écriture
    @assigns    rien
    @ensures    Retourne un pointeur vers stdin si n est 1, NULL sinon 
*/
FILE* primitive302(vim *vm, long n) {
    if (n == 1) {
        return (FILE*)stdin;
    }
    fprintf(stderr, "[primitive302] Paramètre invalide pour obtenir un flux standard.\n");
    vm->running = 0; // on arrête la vm car comportement non défini
    return NULL;
}

/*  @requires   vm : machine virtuelle valide
                file : pointeur vers un fichier ouvert en écriture
    @assigns    rien
    @ensures    Retourne un pointeur vers stdout si n est 3, vers stderr si n est 5, NULL sinon
*/
FILE* primitive304(vim *vm, long n) {
    if (n == 3) {
        return (FILE*)stdout;
    } else if (n == 5) {
        return (FILE*)stderr;
    }
    fprintf(stderr, "[primitive304] Paramètre invalide pour obtenir un flux standard.\n");
    vm->running = 0; // on arrête la vm car comportement non défini
    return NULL;
}

/*  @requires   vm : machine virtuelle valide
                file : pointeur vers un fichier ouvert en écriture
                n : code ASCII d'un caractère
    @assigns    rien
    @ensures    affiche sur le flux f le caractère de code ASCII n
*/
void primitive310(vim *vm, FILE* f, int n) {
    n = decode(n);
    // on vérifie que n est un code ASCII valide
    if (n < 0 || n > 127) {
        fprintf(stderr, "[primitive310] Code ASCII invalide pour un caractère.\n");
        vm->running = 0; // on arrête la vm car comportement non défini
        return;
    }
    fprintf(f, "%c", n);
}


/*  @requires   vm : machine virtuelle valide
    @assigns    vm->running
    @ensures    Appelle la primitive numéro n et retourne la valeur retournée par la primitive
                retourne -1 et arrête vm si le numéro de primitive n'est pas valide
*/
long call_primitive1(vim *vm, int n) {
    switch (n) {
        case 288: {
            // Primitive 288 : fflush sur un fichier
            FILE* file = (FILE*)vm->accu;
            return primitive288(vm, file);
        }
        case 293: {
            // Primitive 293 : lire un caractère dans un fichier
            FILE* file = (FILE*)vm->accu;
            return primitive293(vm, file);
        }
        case 302: {
            // Primitive 302 : obtenir stdin
            long a = vm->accu;
            return (long)primitive302(vm, a);
        }
        case 304: {
            // Primitive 304 : obtenir stdout ou stderr
            long a = vm->accu;
            return (long)primitive304(vm, a);
        }
        default:
            fprintf(stderr, "[call_primitive1] Numéro de primitive invalide : %d\n", n);
            // on arrête la vm car l'effet de la primitive n'est pas défini
            vm->running = 0;
            return -1;
    }
}

/*  @requires   vm : machine virtuelle valide
    @assigns    vm->running
    @ensures    Appelle la primitive numéro n et retourne la valeur retournée par la primitive
                retourne -1 et arrête vm si le numéro de primitive n'est pas valide
*/
long* call_primitive2(vim *vm, int n, long v2) {
    FILE* f;
    switch (n) {
        case 15: {
            // Primitive 15 : création d'un tableau d'entiers
            return (long*) primitive15(vm, vm->accu, v2);
        }
        case 310:
            // Primitive 310 : afficher un caractère sur un flux            
            f= (FILE*)vm->accu;
            // v2 est le code ASCII encodé du caractère à afficher
            // on le décode 
            // on le stock dans un int pour le pouvoir afficher le caractère associé
            int arg = (int)v2; 
            primitive310(vm, f, arg);
            return NULL; // cette primitive ne retourne rien
        default:
            fprintf(stderr, "[call_primitive2] Numéro de primitive invalide : %d\n", n);
            // on arrête la vm car l'effet de la primitive n'est pas défini
            vm->running = 0;
            return NULL;
    }
}

// les autres lanceurs de primitives ne servent à rien car on n'a que des primitives à 1 ou 2 arguments donc ne seront jamais appelés
int call_primitive3(vim *vm, int n, long v2, long v3) {
    switch (n) {
        default:
            fprintf(stderr, "[call_primitive3] Numéro de primitive invalide : %d\n", n);
            // on doit utiliser les arguments v2 et v3 ici sinon warning mais on n'a pas de primitive à 3 arguments
            (void)v2;
            (void)v3;
            // on arrête la vm car l'effet de la primitive n'est pas défini)
            vm->running = 0;
            return 1;
    }
}

// les autres lanceurs de primitives ne servent à rien car on n'a que des primitives à 1 ou 2 arguments donc ne seront jamais appelés
int call_primitive4(vim *vm, int n, long v2, long v3, long v4) {
    switch (n) {
        default:
            fprintf(stderr, "[call_primitive3] Numéro de primitive invalide : %d\n", n);
            // on doit utiliser les arguments v2 et v3 ici sinon warning mais on n'a pas de primitive à 3 arguments
            (void)v2;
            (void)v3;
            (void)v4;
            // on arrête la vm car l'effet de la primitive n'est pas défini)
            vm->running = 0;
            return 1;
    }
}

// les autres lanceurs de primitives ne servent à rien car on n'a que des primitives à 1 ou 2 arguments donc ne seront jamais appelés
int call_primitive5(vim *vm, int n, long v2, long v3, long v4, long v5) {
    switch (n) {
        default:
            fprintf(stderr, "[call_primitive3] Numéro de primitive invalide : %d\n", n);
            // on doit utiliser les arguments v2 et v3 ici sinon warning mais on n'a pas de primitive à 3 arguments
            (void)v2;
            (void)v3;
            (void)v4;
            (void)v5;
            // on arrête la vm car l'effet de la primitive n'est pas défini)
            vm->running = 0;
            return 1;
    }
}

// les autres lanceurs de primitives ne servent à rien car on n'a que des primitives à 1 ou 2 arguments donc ne seront jamais appelés
int call_primitiveP(vim *vm, int n, long* t, int p) {
    switch (n) {
        default:
            fprintf(stderr, "[call_primitiveP] Numéro de primitive invalide : %d\n", n);
            // on doit utiliser les arguments t et p ici sinon warning mais on n'a pas de primitive à p arguments
            (void)t;
            (void)p;
            // on arrête la vm car l'effet de la primitive n'est pas défini)
            vm->running = 0;
            return 1;
    }
}

/*  @requires   vm : machine virtuelle valide
    @assigns    vm->indice ; vm->running
    @ensures   
                vm->indice est incrémenté de 2
*/
void C_CALL1(vim *vm){
    // on vérifie qu'il n'y a pas de dépassement
    // vm->indice ne peut pas être négatif car il est du type unsigned int 
    if (vm->indice + 1 >= vm->c) {
        fprintf(stderr, "[C_CALL1] Dépassement d'indice\n");
        vm->running = 0;
        return;
    }
    // On récupère la valeur non encodée de n
    int n = vm->codes[vm->indice + 1];
    // On appelle la primitive numéro n et on met dans l'accumulateur la valeur retournée par la primitive
    vm->accu = call_primitive1(vm, n);
    // incrémentation de 2 de l'indice pour aller à la prochaine instruction
    vm->indice += 2;
}

/*  @requires   vm : machine virtuelle valide
    @assigns    vm->indice ; vm->running ; vm->accu
    @ensures    vm->accu contient la valeur retournée par la primitive n avec n la valeur encodée suivante du tableau de code
                vm->indice est incrémenté de 2
*/
void C_CALL2(vim *vm){
    // on vérifie qu'il n'y a pas de dépassement
    // vm->indice ne peut pas être négatif car il est du type unsigned int 
    if (vm->indice + 1 >= vm->c) {
        fprintf(stderr, "[C_CALL2] Dépassement d'indice\n");
        vm->running = 0;
        return;
    } 
    // On récupère la valeur non encodée de n
    int n = vm->codes[vm->indice + 1];

    // récupération des arguments de la primitive dans la pile
    int err;
    long v2 = depile(&vm->p, &err);
    if (err) {
        fprintf(stderr, "[C_CALL2] Pile vide, on ne peut pas dépiler.\n");
        vm->running = 0;
        return;
    }
    // On appelle la primitive numéro n et on met dans l'accumulateur la valeur retournée par la primitive
    vm->accu = (long)call_primitive2(vm, n, v2);
    // incrémentation de 2 de l'indice pour aller à la prochaine instruction
    vm->indice += 2;
}

/*  @requires   vm : machine virtuelle valide
    @assigns    vm->indice ; vm->running ; vm->accu
    @ensures    vm->accu contient la valeur retournée par la primitive n avec n la valeur encodée suivante du tableau de code
                vm->indice est incrémenté de 2
*/
void C_CALL3(vim *vm){
    // on vérifie qu'il n'y a pas de dépassement
    // vm->indice ne peut pas être négatif car il est du type unsigned int 
    if (vm->indice + 1 >= vm->c) {
        fprintf(stderr, "[C_CALL3] Dépassement d'indice\n");
        vm->running = 0;
        return;
    }
    // On récupère la valeur non encodée de n
    int n = vm->codes[vm->indice + 1];

    // récupération des arguments de la primitive dans la pile

    int err;
    long v2 = depile(&vm->p, &err);
    if (err) {
        fprintf(stderr, "[C_CALL3] Pile vide, on ne peut pas dépiler.\n");
        vm->running = 0;
        return;
    }
    long v3 = depile(&vm->p, &err);
    if (err) {
        fprintf(stderr, "[C_CALL3] Pile de profondeur insuffisante.\n");
        vm->running = 0;
        return;
    }
    // On appelle la primitive numéro n et on met dans l'accumulateur la valeur retournée par la primitive
    vm->accu = call_primitive3(vm, n, v2, v3);
    // incrémentation de 2 de l'indice pour aller à la prochaine instruction
    vm->indice += 2;
}

/*  @requires   vm : machine virtuelle valide
    @assigns    vm->indice ; vm->running ; vm->accu
    @ensures    vm->accu contient la valeur retournée par la primitive n avec n la valeur encodée suivante du tableau de code
                vm->indice est incrémenté de 2
*/
void C_CALL4(vim *vm){
    // on vérifie qu'il n'y a pas de dépassement
    // vm->indice ne peut pas être négatif car il est du type unsigned int 
    if (vm->indice + 1 >= vm->c) {
        fprintf(stderr, "[C_CALL4] Dépassement d'indice\n");
        vm->running = 0;
        return;
    }
    // On récupère la valeur non encodée de n
    int n = vm->codes[vm->indice + 1];

    // récupération des arguments de la primitive dans la pile

    int err;
    long v2 = depile(&vm->p, &err);
    if (err) {
        fprintf(stderr, "[C_CALL4] Pile vide, on ne peut pas dépiler.\n");
        vm->running = 0;
        return;
    }
    long v3 = depile(&vm->p, &err);
    if (err) {
        fprintf(stderr, "[C_CALL4] Pile de profondeur insuffisante.n");
        vm->running = 0;
        return;
    }
    long v4 = depile(&vm->p, &err);
    if (err) {
        fprintf(stderr, "[C_CALL4] Pile de profondeur insuffisante.\n");
        vm->running = 0;
        return;
    }
    // On appelle la primitive numéro n et on met dans l'accumulateur la valeur retournée par la primitive
    vm->accu = call_primitive4(vm, n, v2, v3, v4);
    // incrémentation de 2 de l'indice pour aller à la prochaine instruction
    vm->indice += 2;
}

/*  @requires   vm : machine virtuelle valide
    @assigns    vm->indice ; vm->running ; vm->accu
    @ensures    vm->accu contient la valeur retournée par la primitive n avec n la valeur encodée suivante du tableau de code
                vm->indice est incrémenté de 2
*/
void C_CALL5(vim *vm){
    // on vérifie qu'il n'y a pas de dépassement
    // vm->indice ne peut pas être négatif car il est du type unsigned int 
    if (vm->indice + 1 >= vm->c) {
        fprintf(stderr, "[C_CALL5] Dépassement d'indice\n");
        vm->running = 0;
        return;
    }
    // On récupère la valeur non encodée de n
    int n = vm->codes[vm->indice + 1];

    // récupération des arguments de la primitive dans la pile

    int err;
    long v2 = depile(&vm->p, &err);
    if (err) {
        fprintf(stderr, "[C_CALL5] Pile vide, on ne peut pas dépiler.\n");
        vm->running = 0;
        return;
    }
    long v3 = depile(&vm->p, &err);
    if (err) {
        fprintf(stderr, "[C_CALL5] Pile de profondeur insuffisante.\n");
        vm->running = 0;
        return;
    }
    long v4 = depile(&vm->p, &err);
    if (err) {
        fprintf(stderr, "[C_CALL5] Pile de profondeur insuffisante.\n");
        vm->running = 0;
        return;
    }
    long v5 = depile(&vm->p, &err);
    if (err) {
        fprintf(stderr, "[C_CALL5] Pile de profondeur insuffisante.\n");
        vm->running = 0;
        return;
    }
    // On appelle la primitive numéro n et on met dans l'accumulateur la valeur retournée par la primitive
    vm->accu = call_primitive5(vm, n, v2, v3, v4, v5);
    // incrémentation de 2 de l'indice pour aller à la prochaine instruction
    vm->indice += 2;
}

/*  @requires   vm : machine virtuelle valide
    @assigns    vm->indice ; vm->running ; vm->accu
    @ensures    vm->accu contient la valeur retournée par la primitive n avec n la valeur encodée suivante du tableau de code
                vm->indice est incrémenté de 2
*/
void C_CALLN(vim *vm){
    // on vérifie qu'il n'y a pas de dépassement
    // vm->indice ne peut pas être négatif car il est du type unsigned int 
    if (vm->indice + 2 >= vm->c) {
        fprintf(stderr, "[C_CALLN] Dépassement d'indice\n");
        vm->running = 0;
        return;
    }
    // On récupère la valeur non encodée de p
    int p = vm->codes[vm->indice + 1];
    // On récupère la valeur non encodée de n
    int n = vm->codes[vm->indice + 2];

    // récupération des arguments de la primitive dans la pile

    long *t = malloc(p * sizeof(long));
    if (t == NULL) {
        fprintf(stderr, "[C_CALLN] Erreur d'allocation mémoire pour les arguments de la primitive.\n");
        vm->running = 0;
        return;
    }
    t[0] = vm->accu;
    int err;
    for (int i=1 ; i < p; i++) {
        t[i] = depile(&vm->p, &err);
        if (err) {
            fprintf(stderr, "[C_CALLN] Pile vide, on ne peut pas dépiler.\n");
            vm->running = 0;
            free(t);
            return;
        }
    }
    // On appelle la primitive numéro n et on met dans l'accumulateur la valeur retournée par la primitive
    vm->accu = call_primitiveP(vm, n, t, p);
    // on libère le tableau d'arguments
    free(t);
    // incrémentation de 2 de l'indice pour aller à la prochaine instruction
    vm->indice += 3;
}



////////////////////////////////// Mémoire globale /////////////////////////////////////////



/*  @requires   vm : machine virtuelle valide
    @assigns    vm->indice ; vm->running ; vm->accu
    @ensures    vm->accu contient la valeur de la variable globale d'indice n avec n la valeur encodée suivante du tableau de code
                vm->indice est incrémenté de 2
*/
void GETGLOBAL(vim *vm){
    // on vérifie qu'il n'y a pas de dépassement
    // vm->indice ne peut pas être négatif car il est du type unsigned int 
    if (vm->indice + 1 >= vm->c) {
        fprintf(stderr, "[GETGLOBAL] Dépassement d'indice\n");
        vm->running = 0;
        return;
    }
    int n = vm->codes[vm->indice + 1];
    // on vérifie qu'on ne sort pas du tableau de valeurs globales
    if (n >= (int)vm->v) {
            fprintf(stderr, "[GETGLOBAL] Indice global hors limites: %d\n", n);
            vm->running = 0; return;
        }
    // récupération de la valeur de la variable globale dans le tableau des variables globales
    vm->accu = vm->valeurs[n];
    // incrémentation de 2 de l'indice pour aller à la prochaine instruction
    vm->indice += 2;
}


/*  @requires   vm : machine virtuelle valide
    @assigns    vm->indice ; vm->running ; vm->accu ; vm->p
    @ensures    vm->accu contient la valeur de la variable globale d'indice n avec n la valeur encodée suivante du tableau de code
                la valeur du début d'appel de l'accumulateur est empilée
                vm->indice est incrémenté de 2
*/
void PUSHGETGLOBAL(vim *vm){
    // on empile l'accumulateur + incrémentation discrte de l'indice de 1 
    PUSH(vm); // indice incrémenté de 1
    vm->indice--; // on remet l'indice à la bonne valeur
    GETGLOBAL(vm); // indice incrémenté de 2 à la fin
}

/*  @requires   vm : machine virtuelle valide
    @assigns    vm->indice ; vm->running
    @ensures    la variable globale d'indice n prend la valeur de l'accumulateur avec n la valeur encodée suivante du tableau de code
                vm->accu prend la valeur 1
                vm->indice est incrémenté de 2
*/
void SETGLOBAL(vim *vm){
    // on vérifie qu'il n'y a pas de dépassement
    // vm->indice ne peut pas être négatif car il est du type unsigned int 
    if (vm->indice + 1 >= vm->c) {
        fprintf(stderr, "[SETGLOBAL] Dépassement d'indice\n");
        vm->running = 0;
        return;
    }
    int n = vm->codes[vm->indice + 1];
    // on vérifie qu'on ne sort pas du tableau de valeurs globales
    if (n >= (int)vm->v) { 
        fprintf(stderr, "[SETGLOBAL] Indice global hors limites: %d\n", n);
        vm->running = 0; 
        return;
    }
    // on met dans la variable globale d'indice n la valeur de l'accumulateur
    vm->valeurs[n] = vm->accu;
    vm->accu = 1;
    // incrémentation de 2 de l'indice pour aller à la prochaine instruction
    vm->indice += 2;
}




////////////////////////////////// Création de blocs /////////////////////////////////////////


/*  @requires   vm : machine virtuelle valide
                vm->p a une profondeur suffisante (n-1)
    @assigns    vm->indice ; vm->running ; vm->accu ; vm->p
    @ensures    On alloue un tableau de valeurs de taille n avec n la valeur encodée suivante du tableau de code dont la case d'indice 0 vaut l'accumulateur et les autres cases sont remplies en dépilant la pile. On met dans l'accumulateur ce tableau (en faisant un conversion explicite).
                vm->indice est incrémenté de 3
*/
void MAKEBLOCK(vim *vm) {
    // on vérifie qu'il n'y a pas de dépassement
    // vm->indice ne peut pas être négatif car il est du type unsigned int 
    if (vm->indice + 1 >= vm->c) {
        fprintf(stderr, "[MAKEBLOCK] Dépassement d'indice\n");
        vm->running = 0;
        return;
    }
    // récupération de la taille du tableau
    int n = vm->codes[vm->indice + 1];

    long* tab = malloc(n * sizeof(long));
    if (tab == NULL) {
        fprintf(stderr, "[MAKEBLOCK] Erreur d'allocation mémoire\n");
        vm->running = 0;
        return;
    }
    tab[0] = vm->accu;
    // on remplit le tableau en dépilant la pile
    int err;
    for (int i = 1; i < n; i++) {
        long v = depile(&vm->p, &err);
        if (err) {
            fprintf(stderr, "[MAKEBLOCK] Pile vide, on ne peut pas dépiler.\n");
            vm->running = 0;
            return;
        }
        tab[i] = v;
    }
    // on met dans l'accumulateur le tableau créé (avec conversion explicite)
    vm->accu = (long)tab;
    // incrémentation de 3 (donc saut d'une instruction)
    vm->indice += 3;
}

/*  @requires   vm : machine virtuelle valide
    @assigns    vm->indice ; vm->running ; vm->accu
    @ensures    On alloue un tableau de valeurs de taille 1 dont la case d'indice 0 vaut l'accumulateur. On met dans l'accumulateur ce tableau (en faisant un conversion explicite).
                vm->indice est incrémenté de 2
*/
void MAKEBLOCK1(vim *vm) {
    long* tab = malloc(1 * sizeof(long));
    if (tab == NULL) {
        fprintf(stderr, "[MAKEBLOCK1] Erreur d'allocation mémoire\n");
        vm->running = 0;
        return;
    }
    tab[0] = vm->accu;
    vm->accu = (long)tab;
    // incrémentation de 2
    vm->indice += 2;
}

/*  @requires   vm : machine virtuelle valide
                vm->p a une profondeur suffisante (1)
    @assigns    vm->indice ; vm->running ; vm->accu ; vm->p
    @ensures    On alloue un tableau de valeurs de taille 2 dont la case d'indice 0 vaut l'accumulateur et l'autre case vaut la valeur dépilée. On met dans l'accumulateur ce tableau (en faisant un conversion explicite).
                vm->indice est incrémenté de 2
*/
void MAKEBLOCK2(vim *vm) {
    long* tab = malloc(2 * sizeof(long));
    if (tab == NULL) {
        fprintf(stderr, "[MAKEBLOCK2] Erreur d'allocation mémoire\n");
        vm->running = 0;
        return;
    }
    tab[0] = vm->accu;
    int err;
    long v = depile(&vm->p, &err);
    if (err) {
        fprintf(stderr, "[MAKEBLOCK2] Pile vide.\n");
        vm->running = 0;
        return;
    }
    tab[1] = v;
    vm->accu = (long)tab;
    // incrémentation de 2
    vm->indice += 2;
}

/*  @requires   vm : machine virtuelle valide
                vm->p a une profondeur suffisante (2)
    @assigns    vm->indice ; vm->running ; vm->accu ; vm->p
    @ensures    On alloue un tableau de valeurs de taille 3 dont la case d'indice 0 vaut l'accumulateur et les autres cases valent les valeurs dépilées. On met dans l'accumulateur ce tableau (en faisant un conversion explicite).
                vm->indice est incrémenté de 2
*/
void MAKEBLOCK3(vim *vm) {
    long* tab = malloc(3 * sizeof(long));
    if (tab == NULL) {
        fprintf(stderr, "[MAKEBLOCK3] Erreur d'allocation mémoire\n");
        vm->running = 0;
        return;
    }
    tab[0] = vm->accu;
    int err;
    long v2 = depile(&vm->p, &err);
    if (err) {
        fprintf(stderr, "[MAKEBLOCK3] Pile vide.\n");
        vm->running = 0;
        return;
    }
    tab[1] = v2;
    long v3 = depile(&vm->p, &err);
    if (err) {
        fprintf(stderr, "[MAKEBLOCK3] Pile de profondeur insuffisante, on ne peut pas dépiler.\n");
        vm->running = 0;
        return;
    }
    tab[2] = v3;
    vm->accu = (long)tab;
    // incrémentation de 2
    vm->indice += 2;
}


////////////////////////////// Accès/écriture dans les blocs /////////////////////////////////


/*  @requires   vm : machine virtuelle valide
    @assigns    vm->indice ; vm->accu
    @ensures    vm->accu contient la valeur de la case d'indice 0 du tableau pointé par l'accumulateur
                vm->indice est incrémenté de 1
*/
void GETFIELD0(vim *vm) {
    long* tab = (long*) vm->accu;
    vm->accu = tab[0];
    // incrémentation de l'indice pour aller à la prochaine instruction
    vm->indice++;
}

/*  @requires   vm : machine virtuelle valide
    @assigns    vm->indice ; vm->accu
    @ensures    vm->accu contient la valeur de la case d'indice 1 du tableau pointé par l'accumulateur
                vm->indice est incrémenté de 1
*/
void GETFIELD1(vim *vm) {
    long* tab = (long*) vm->accu;
    vm->accu = tab[1];
    // incrémentation de l'indice pour aller à la prochaine instruction
    vm->indice++;
}

/*  @requires   vm : machine virtuelle valide
    @assigns    vm->indice ; vm->accu
    @ensures    vm->accu contient la valeur de la case d'indice 2 du tableau pointé par l'accumulateur
                vm->indice est incrémenté de 1
*/
void GETFIELD2(vim *vm) {
    long* tab = (long*) vm->accu;
    vm->accu = tab[2];
    // incrémentation de l'indice pour aller à la prochaine instruction
    vm->indice++;
}

/*  @requires   vm : machine virtuelle valide
    @assigns    vm->indice ; vm->accu
    @ensures    vm->accu contient la valeur de la case d'indice 3 du tableau pointé par l'accumulateur
                vm->indice est incrémenté de 1
*/
void GETFIELD3(vim *vm) {
    long* tab = (long*) vm->accu;
    vm->accu = tab[3];
    // incrémentation de l'indice pour aller à la prochaine instruction
    vm->indice++;
}

/*  @requires   vm : machine virtuelle valide
    @assigns    vm->indice ; vm->accu ; vm->running
    @ensures    vm->accu contient la valeur de la case d'indice n du tableau pointé par l'accumulateur avec n la valeur encodée suivante du tableau de code
                vm->indice est incrémenté de 2
*/
void GETFIELD(vim *vm) {
    // on vérifie qu'il n'y a pas de dépassement
    // vm->indice ne peut pas être négatif car il est du type unsigned int 
    if (vm->indice + 1 >= vm->c) {
        fprintf(stderr, "[GETFIELD] Dépassement d'indice\n");
        vm->running = 0;
        return;
    }
    int n = vm->codes[vm->indice + 1];
    long* tab = (long*) vm->accu;
    vm->accu = tab[n];
    // incrémentation de l'indice pour aller à la prochaine instruction
    vm->indice += 2;
}


/*  @requires   vm : machine virtuelle valide
                vm->p non vide
    @assigns    vm->indice ; vm->accu ; vm->running ; vm->p
    @ensures    la valeur de la case d'indice n du tableau pointé par l'accumulateur contient la valeur dépilée
                vm->accu prend la valeur 1
                vm->indice est incrémenté de 1
*/
void SETFIELDN(vim *vm, int n) {
    long* tab = (long*) vm->accu;
    int err;
    long v = depile(&vm->p, &err);
    if (err) {
        fprintf(stderr, "[SETFIELDN] Pile de profondeur insuffisante, on ne peut pas dépiler.\n");
        vm->running = 0;
        return;
    }
    tab[n] = v;
    vm->accu = 1; // énoncé : on met 1 dans l'accumulateur
    // incrémentation de l'indice pour aller à la prochaine instruction
    vm->indice++;
}

/*  @requires   vm : machine virtuelle valide
                vm->p non vide
    @assigns    vm->indice ; vm->accu ; vm->running ; vm->p
    @ensures    la valeur de la case d'indice 0 du tableau pointé par l'accumulateur contient la valeur dépilée
                vm->accu prend la valeur 1
                vm->indice est incrémenté de 1
*/
void SETFIELD0(vim *vm) {
    SETFIELDN(vm, 0);
}

/*  @requires   vm : machine virtuelle valide
                vm->p non vide
    @assigns    vm->indice ; vm->accu ; vm->running ; vm->p
    @ensures    la valeur de la case d'indice 1 du tableau pointé par l'accumulateur contient la valeur dépilée
                vm->accu prend la valeur 1
                vm->indice est incrémenté de 1
*/
void SETFIELD1(vim *vm) {
    SETFIELDN(vm, 1);
}

/*  @requires   vm : machine virtuelle valide
                vm->p non vide
    @assigns    vm->indice ; vm->accu ; vm->running ; vm->p
    @ensures    la valeur de la case d'indice 2 du tableau pointé par l'accumulateur contient la valeur dépilée
                vm->accu prend la valeur 1
                vm->indice est incrémenté de 1
*/
void SETFIELD2(vim *vm) {
    SETFIELDN(vm, 2);
}

/*  @requires   vm : machine virtuelle valide
                vm->p non vide
    @assigns    vm->indice ; vm->accu ; vm->running ; vm->p
    @ensures    la valeur de la case d'indice 3 du tableau pointé par l'accumulateur contient la valeur dépilée
                vm->accu prend la valeur 1
                vm->indice est incrémenté de 1
*/
void SETFIELD3(vim *vm) {
    SETFIELDN(vm, 3);
}

/*  @requires   vm : machine virtuelle valide
                vm->p non vide
    @assigns    vm->indice ; vm->accu ; vm->running ; vm->p
    @ensures    la valeur de la case d'indice n du tableau pointé par l'accumulateur contient la valeur dépilée avec n la valeur encodée suivante du tableau de code
                vm->accu prend la valeur 1 
                vm->indice est incrémenté de 2
*/
void SETFIELD(vim *vm) {
    // on vérifie qu'il n'y a pas de dépassement
    // vm->indice ne peut pas être négatif car il est du type unsigned int 
    if (vm->indice + 1 >= vm->c) {
        fprintf(stderr, "[SETFIELD] Dépassement d'indice\n");
        vm->running = 0;
        return;
    }
    // récupération de la taille du tableau
    int n = vm->codes[vm->indice + 1];

    // On remplace le contenu de la case d'indice n du tableau pointé par l'accumulateur par une valeur qu'on dépile
    SETFIELDN(vm, n); // incrémente l'indice de 1
    // on incrémente encore l'indice pour atteindre la prochaine instruction
    vm->indice++;
}

/*  @requires   vm : machine virtuelle valide
                l’accumulateur doit pointer vers un tableau valide.
                vm->p non vide
    @assigns    vm->indice ; vm->accu ; vm->running ; vm->p
    @ensures    l'accumulateur contient la valeur de la case d'indice n du tableau pointé par l'accumulateur au début de l'execution de GETVECTITEM avec n la valeur dépilée
                vm->indice est incrémenté de 1
*/
void GETVECTITEM(vim *vm) {
    int err;
    long n = depile(&vm->p, &err);
    n = decode(n);
    if (err) {
        fprintf(stderr, "[GETVECTITEM] Pile de profondeur insuffisante, on ne peut pas dépiler.\n");
        vm->running = 0;
        return;
    }
    long* tab = (long*) vm->accu;
    vm->accu = tab[n];
    // incrémentation de l'indice pour aller à la prochaine instruction
    vm->indice++;
}

/*  @requires   vm : machine virtuelle valide
                vm->p de pronfondeur au moins 2
    @assigns    vm->indice ; vm->accu ; vm->running ; vm->p
    @ensures    la case d'indice n du tableau pointé par l'accumulateur contient la valeur v avec n et v les valeurs dépilées
                vm->accu prend la valeur 1 
                vm->indice est incrémenté de 1
*/
void SETVECTITEM(vim *vm) {
    // récupération de l'indice n
    int err;
    long n = depile(&vm->p, &err);
    if (err) {
        fprintf(stderr, "[SETVECTITEM] Pile de profondeur insuffisante, on ne peut pas dépiler.\n");
        vm->running = 0;
        return;
    }
    n = decode(n);
    // récupération de la valeur à insérer
    long v = depile(&vm->p, &err);
    if (err) {
        fprintf(stderr, "[SETVECTITEM] Pile de profondeur insuffisante, on ne peut pas dépiler.\n");
        vm->running = 0;
        return;
    }
    long* tab = (long*) vm->accu;
    tab[n] = v;
    vm->accu = 1;
    // incrémentation de l'indice pour aller à la prochaine instruction
    vm->indice++;
}

/*  @requires   vm : machine virtuelle valide
    @assigns    vm->indice ; vm->running ; vm->accu
    @ensures    vm->accu contient la valeur de la case d'indice p du tableau pointé par la valeur globale d'indice n avec n et p les valeurs encodées suivantes du tableau de code
                vm->indice est incrémenté de 3
*/
void GETGLOBALFIELD(vim *vm) {
    // on vérifie qu'il n'y a pas de dépassement
    // vm->indice ne peut pas être négatif car il est du type unsigned int
    if (vm->indice + 2 >= vm->c) {
        fprintf(stderr, "[GETGLOBALFIELD] Dépassement d'indice\n");
        vm->running = 0;
        return;
    }
    int n = vm->codes[vm->indice + 1];

    int p = vm->codes[vm->indice + 2];

    // on vérifie qu'on ne sort pas du tableau de valeurs globales
    if (n >= (int)vm->v) { 
        fprintf(stderr, "[GETGLOBALFIELD] Indice global hors limites: %d\n", n);
        vm->running = 0; return;
    }
    long *tab = (long*) vm->valeurs[n];
    vm->accu = tab[p];
    vm->indice += 3;
}

/*  @requires   vm : machine virtuelle valide
    @assigns    vm->indice ; vm->running ; vm->accu ; vm->p
    @ensures    la case d'indice p du tableau pointé par la valeur globale d'indice n contient la valeur de l'accumulateur avec n et p les valeurs encodées suivantes du tableau de code
                la valeur du début d'appel de l'accumulateur est empilée
                vm->indice est incrémenté de 3
*/
void PUSHGETGLOBALFIELD(vim *vm) {
    // on empile l'accumulateur + incrémentation discrte de l'indice de 1 
    PUSH(vm);  // incrémentation de l'indice de 1
    vm->indice--; // on remet la bonne valeur d'indice
    GETGLOBALFIELD(vm); // incrémentation de l'indice de 3 à la fin seulement
}

/*  @requires   vm : machine virtuelle valide
    @assigns    vm->indice ; vm->running ; vm->accu
    @ensures    la case d'indice p du tableau pointé par la valeur globale d'indice n contient la valeur de l'accumulateur avec n et p les valeurs encodées suivantes du tableau de code
                vm->accu prend la valeur 1
                vm->indice est incrémenté de 3
*/
void OFFSETREF(vim *vm) {
    // on vérifie qu'il n'y a pas de dépassement
    // vm->indice ne peut pas être négatif car il est du type unsigned int 
    if (vm->indice + 1 >= vm->c) {
        fprintf(stderr, "[OFFSETREF] Dépassement d'indice\n");
        vm->running = 0;
        return;
    }
    // récupération de la taille du tableau
    int n = vm->codes[vm->indice + 1];
    long* tab = (long*) vm->accu;
    long m = tab[0];
    m = decode(m);
    tab[0] = encode(m + n);
    vm->accu = 1;
    // incrémentation de 2 (donc saut d'une instruction)
    vm->indice += 2;
}

//////////////////////////////////////// Atomes //////////////////////////////////////////////

/*  @requires   vm : machine virtuelle valide
    @assigns    vm->indice ; vm->accu
    @ensures    vm->accu contient la valeur de l'atome d'indice 0
                vm->indice est incrémenté de 1
*/
void ATOM0(vim *vm) {
    // cast correct car atomes[0] est de type long*
    vm->accu = (long)atomes[0];
    vm->indice++;
}

/*  @requires   vm : machine virtuelle valide
    @assigns    vm->indice ; vm->running ; vm->accu
    @ensures    vm->accu contient la valeur de l'atome d'indice n avec n la valeur encodée suivante du tableau de code
                vm->indice est incrémenté de 2
*/
void ATOM(vim *vm) {
    // on vérifie qu'il n'y a pas de dépassement
    // vm->indice ne peut pas être négatif car il est du type unsigned int 
    if (vm->indice + 1 >= vm->c) {
        fprintf(stderr, "[ATOM] Dépassement d'indice\n");
        vm->running = 0;
        return;
    }
    int n = vm->codes[vm->indice + 1];
    
    vm->accu = (long)atomes[n];
    vm->indice += 2;
}

/*  @requires   vm : machine virtuelle valide
    @assigns    vm->indice ; vm->accu
    @ensures    le contenu de l'accumulateur est empilée
                vm->accu contient la valeur de l'atome d'indice 0
                vm->indice est incrémenté de 1
*/
void PUSHATOM0(vim *vm) {
    PUSH(vm); // incrémente de 1
    vm->indice--; // on remet l'indice à la bonne valeur
    ATOM0(vm); // incrémente de 1 à la fin
}

/*  @requires   vm : machine virtuelle valide
    @assigns    vm->indice ; vm->accu
    @ensures    le contenu de l'accumulateur est empilée
                vm->accu contient la valeur de l'atome d'indice n avec n la valeur encodée suivante du tableau de code
                vm->indice est incrémenté de 1
*/
void PUSHATOM(vim *vm) {
    PUSH(vm); // incrémente de 1
    vm->indice--; // on remet l'indice à la bonne valeur
    ATOM(vm); // incrémente de 1 à la fin

}