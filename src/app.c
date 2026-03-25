#include "instructions.h"
#include "objets.h"


// Définition des structures utilisées 
// On redéfinit la structure ici pour éviter de mettre du code C dans le fichier .h

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

/* @requires vm : une machine virtuelle valide
   @assigns vm->indice, vm->accu, vm->p, vm->running, vm->valeurs
   @ensures exécute l'instruction pointée par l'indice de la machine virtuelle
*/
void App(vim *vm) {
    /* printf("\n"); fflush(stdin);
    printf("indice : %u\n", vm->indice); fflush(stdin);
    printf("top : %d\n", vm->p.top); fflush(stdin);
    printf("accu : %ld\n", vm->accu); fflush(stdin);
 */
    // on vérifie que l'indice est bien dans les limites du tableau de codes
    if (vm->indice >= vm->c) {
        fprintf(stderr, "[App] Indice hors limites");
        vm->running = 0;
        return;
    } else {
        // on récupère le code de l'instruction à exécuter
        int code = vm->codes[vm->indice];

        // on exécute l'instruction correspondante
        switch (code) {

            /////////////// Instructions de base /////////////////

            case 0:   ACC0(vm); break;
            case 1:   ACC1(vm); break;
            case 2:   ACC2(vm); break;
            case 3:   ACC3(vm); break;
            case 4:   ACC4(vm); break;
            case 5:   ACC5(vm); break;
            case 6:   ACC6(vm); break;
            case 7:   ACC7(vm); break;
            case 8:   ACC(vm);  break;

            case 9:   PUSH(vm); break;
            case 10:  PUSHACC0(vm); break;
            case 11:  PUSHACC1(vm); break;
            case 12:  PUSHACC2(vm); break;
            case 13:  PUSHACC3(vm); break;
            case 14:  PUSHACC4(vm); break;
            case 15:  PUSHACC5(vm); break;
            case 16:  PUSHACC6(vm); break;
            case 17:  PUSHACC7(vm); break;
            case 18:  PUSHACC(vm);  break;

            case 19:  POP(vm); break;
            case 20:  ASSIGN(vm); break;

            case 143: STOP(vm); break;
            case 92:  CHECK_SIGNALS(vm); break;

            /////////////////// Branchements //////////////////

            case 84:  BRANCH(vm); break;
            case 85:  BRANCHIF(vm); break;
            case 86:  BRANCHIFNOT(vm); break;
            case 87:  SWITCH(vm); break;
            case 88:  BOOLNOT(vm); break;
            case 121: EQ(vm); break;
            case 122: NEQ(vm); break;

            //////////////// Entiers //////////////////

            case 99:  CONST0(vm); break;
            case 100: CONST1(vm); break;
            case 101: CONST2(vm); break;
            case 102: CONST3(vm); break;
            case 103: CONSTINT(vm); break;

            case 104: PUSHCONST0(vm); break;
            case 105: PUSHCONST1(vm); break;
            case 106: PUSHCONST2(vm); break;
            case 107: PUSHCONST3(vm); break;
            case 108: PUSHCONSTINT(vm); break;

            case 109: NEGINT(vm); break;
            case 110: ADDINT(vm); break;
            case 111: SUBINT(vm); break;
            case 112: MULINT(vm); break;
            case 113: DIVINT(vm); break;
            case 114: MODINT(vm); break;
            case 115: ANDINT(vm); break;
            case 116: ORINT(vm);  break;
            case 117: XORINT(vm); break;
            case 118: LSLINT(vm); break;
            case 119: LSRINT(vm); break;
            case 120: ASRINT(vm); break;

            case 123: LTINT(vm); break;
            case 124: LEINT(vm); break;
            case 125: GTINT(vm); break;
            case 126: GEINT(vm); break;
            
            case 137: ULTINT(vm); break;
            case 138: UGEINT(vm); break;

            case 127: OFFSETINT(vm); break;
            case 129: ISINT(vm); break;


            case 131: BEQ(vm); break;
            case 132: BNEQ(vm); break;
            case 133: BLTINT(vm); break;
            case 134: BLEINT(vm); break;
            case 135: BGTINT(vm); break;
            case 136: BGEINT(vm); break;
            case 139: BULTINT(vm); break;
            case 140: BUGEINT(vm); break;

            ///////////// Primitives ///////////////

            case 93: C_CALL1(vm); break;
            case 94: C_CALL2(vm); break;
            case 95: C_CALL3(vm); break;
            case 96: C_CALL4(vm); break;
            case 97: C_CALL5(vm); break;
            case 98: C_CALLN(vm); break;

            ///////////// Mémoire globale /////////////

            case 53: GETGLOBAL(vm); break;
            case 54: PUSHGETGLOBAL(vm); break;
            case 57: SETGLOBAL(vm); break;

            ///////// Création de blocs /////////////

            case 62: MAKEBLOCK(vm);  break;
            case 63: MAKEBLOCK1(vm); break;
            case 64: MAKEBLOCK2(vm); break;
            case 65: MAKEBLOCK3(vm); break;

            ///////// Accès/écriture dans les blocs ///////////////

            case 67: GETFIELD0(vm); break;
            case 68: GETFIELD1(vm); break;
            case 69: GETFIELD2(vm); break;
            case 70: GETFIELD3(vm); break;
            case 71: GETFIELD(vm);  break;

            case 73: SETFIELD0(vm); break;
            case 74: SETFIELD1(vm); break;
            case 75: SETFIELD2(vm); break;
            case 76: SETFIELD3(vm); break;
            case 77: SETFIELD(vm);  break;

            case 80: GETVECTITEM(vm); break;
            case 81: SETVECTITEM(vm); break;
            case 55: GETGLOBALFIELD(vm); break;
            case 56: PUSHGETGLOBALFIELD(vm); break;
            case 128: OFFSETREF(vm); break;

            ////////////////// ATOMES /////////////////////

            case 58:  ATOM0(vm); break;
            case 59:  ATOM(vm);  break;
            case 60:  PUSHATOM0(vm); break;
            case 61:  PUSHATOM(vm);  break;

            default:
                fprintf(stderr, "[App] Code d'instruction inconnu: %d\n", code);
                vm->running = 0;
                break;
        }

    }
}