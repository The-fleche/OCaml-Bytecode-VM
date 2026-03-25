#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include <errno.h>
#include <string.h>
#include <ctype.h>

// on importe les autres fichiers du projet
#include "objets.h"
#include "instructions.h"
#include "app.h"

void format_verif(FILE* f, unsigned int *c, unsigned int *v);

// On définit les structures utilisées

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

/* int is_pointer(long val) {
    return (val % 2 == 0) && (val != 0); // 0 est souvent NULL, donc pas un bloc valide
} */

/*  @requires 
    @assigns 
    @ensures
*/
/* c ou v doivent être différent de 0 sinon ce n'est pas considérer comme un format de fichier valide*/
void format_verif(FILE* f, unsigned int *c, unsigned int *v){

    char buf[6];
    fread(&buf, sizeof(char), 5, f);
    // Si la première ligne du fichier n'est pas SOBF on renvoie une erreur
    if (strcmp(buf, "SOBF\n") != 0) { 
        fprintf(stderr, "[Invalid Format]"); 
        exit(1);
    }
    // On regarde maintenant la deuxième ligne du fichier

    int ch;
    int nb = 0;
    /* Terminaison de boucle car soit on avance dans le fichier soit on est à la fin et on quitte */
    // on parcours chacun des caractères temps qu'on obtient des chiffres 
    while ((ch  = fgetc(f)) != EOF && isdigit(ch)) {
        if (ch < 0) {
            fprintf(stderr, "[Invalid Format]");
            exit(1);
        } else {
            nb = 10*nb + (ch - '0');
        }
    }
    if (ch != ' ' || nb == 0) {
        fprintf(stderr, "[Invalid Format]");
        exit(1);
    }
    *c = nb;
    nb = 0;
    /* Terminaison de boucle car soit on avance dans le fichier soit on est à la fin et on quitte */
    // on parcours chacun des caractères temps qu'on obtient des chiffres 
    while ((ch  = fgetc(f)) != EOF && isdigit(ch)) {
        if (ch < 0) {
            fprintf(stderr, "[Invalid Format]");
            exit(1);
        } else {
            nb = 10*nb + (ch - '0');
        }
    }
    if (ch != '\n') {
        fprintf(stderr, "[Invalid Format]");
        exit(1);
    }
    *v = nb;
}



int main(int argc, char* argv[]){ 
    // Initialisation des variables
    int bonus = 0;
    unsigned int c = 0;  // représente nombre de codes dans le tableau de codes
    unsigned int v = 0; //  nombre de valeurs dans le tableau de valeurs globales
    // on initialise le tableau des atomes
    init_atomes();
    // Vérification du format d'appel du programme
    if (argc != 3 && argc != 2) {
        fprintf(stderr, "usage: ./fichier.c chemin_du_fichier [--print-end-machine]\n");
        exit(1);
    } else if (argc == 3) {
        // on vérifie que l'argument bonus est le bon
        if (strcmp(argv[2], "--print-end-machine") == 0) {
            bonus = 1;
        } else {
            fprintf(stderr, "usage: ./fichier.c chemin_du_fichier [--print-end-machine]\n");
            exit(1);
        }
    }

    // Ouverture du fichier
    FILE *f = fopen(argv[1], "r");
    if (f == NULL) {
        perror("Erreur lors de l'ouverture du fichier");
        return 1;
    }

    
    // Vérification du bon format du fichier 
    // on récupère au passage les données contenues dans la deuxième ligne
    // Attention on doit avoir c et v non nuls sinon c'est considéré comme un format non valide
    format_verif(f, &c, &v);
    // mise en place de la VM

    vim vm;
    vm.c = c;
    vm.v = v;

    vm.indice = 0;
    vm.accu = 1;
    vm.running = 1;
    
    init_pile(&vm.p);
    // Lecture du tableau de codes

    vm.codes = malloc(c * sizeof(int));
    // on vérifie qu'on a bien pu allouer l'espace pour stocker le tableau de codes
    if (vm.codes == NULL) {
        fprintf(stderr, "[malloc] tableau de codes");
        fclose(f);
        free(vm.codes);
        exit(1);
    }

    // on récupère les codes et on vérifie qu'on a bien lu tous les codes
    if (fread(vm.codes, sizeof(int), c, f) != c) {
        fprintf(stderr, "[fread] le tableau de codes n'a pas pu être lu correctement");
        fclose(f);
        free(vm.codes);
        exit(1);
    }

    // Lecture du tableau de valeurs
    vm.valeurs = malloc(v * sizeof(long));
    // on vérifie qu'on a bien pu allouer l'espace pour stocker le tableau de valeurs
    if (vm.valeurs == NULL) {
        fprintf(stderr, "[malloc] tableau de codes");
        fclose(f);
        free(vm.codes);
        free(vm.valeurs);
        exit(1);
    }
    // on récupère les valeurs et on vérifie qu'on a bien lu toutes les valeurs
    if (fread(vm.valeurs, sizeof(long), v, f) != v) {
        fprintf(stderr, "[fread] le tableau de valeurs n'a pas pu être lu correctement");
        fclose(f);
        free(vm.valeurs);
        free(vm.codes);
        exit(1);
    }    
    // fonctionnement de la machine
    // terminaison de boucle car vm.c - vm.indice est une suite d'entiers naturels décroissante
    // donc forcément on atteindra un indice hors limite ou l'instruction STOP sera appelée
    // ce qui mettra vm.running à 0 et terminera la boucle    
    while (vm.running == 1) {
        App(&vm);
    }

    // Affichage du résultat 
    if (bonus == 0) {
        printf("Accumulator: %ld\n", vm.accu);
    } else { 
        // Affichage spécial car on a le bon second argument 
        printf("\nIndex: %d\n", vm.indice);
        // On décode la valeur de l'accumulateur et on l'affiche
        printf("Accumulator: %ld\n", vm.accu);
        // Une ligne contenant Stack:, puis, à la ligne, les valeurs contenues dans la pile,
        // une par ligne, en commençant par celle au sommet ;
        printf("Stack:\n");
        for (int i = vm.p.top; i >= 0; i--) {
            printf("%ld\n", vm.p.data[i]);
        }
        // Une ligne contenant Global:, puis, à la ligne, 
        // les valeurs contenues dans le tableau de valeurs globales, une par ligne, 
        // en les précédant du numéro d'indice dans le tableau.
        printf("Global:\n");
        for (unsigned int i = 0; i < vm.v; i++) {
            printf("%u %ld\n", i, vm.valeurs[i]);
            
/*             if ((i == 12 || i == 13) && is_pointer(vm.valeurs[i])) {
                long* adr = (long*)vm.valeurs[i];
                printf(" -> [Block @%p] ", (void*)adr);
                // On affiche quelques valeurs pour vérifier (attention aux blocs vides)
                // Ici on suppose que le bloc a au moins une taille de 3 pour l'affichage
                printf("{ ");
                for(int k=0; k<3; k++) {
                   // Affiche brute. Pour avoir la vraie valeur int, il faudrait décoder.
                   printf("%ld ", adr[k]); 
                }
                printf("... }");
        } */
    }
    printf("\n");
    // on ferme le fichier avant de terminer le programme
    // on libère l'espace aussi
    free(vm.codes);
    free(vm.valeurs);
    fclose(f);

    return 0;
}
}
