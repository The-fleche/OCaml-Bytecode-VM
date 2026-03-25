#ifndef INSTRUCTIONS_H

#define INSTRUCTIONS_H
#include "objets.h"

typedef struct virtual_machine vim;

// fonctions utilitaires

long encode(long n);
long decode(long n);
long abs_long(long n);
void init_atomes();

// Instructions de bases

void ACC0(vim *vm);
void ACCN(vim *vm, int n);
void ACC1(vim *vm);
void ACC2(vim *vm);
void ACC3(vim *vm);
void ACC4(vim *vm);
void ACC5(vim *vm);
void ACC6(vim *vm);
void ACC7(vim *vm);
void ACC(vim *vm);

void PUSH(vim *vm);
void PUSHACCN(vim *vm, int n);
void PUSHACC0(vim *vm);
void PUSHACC1(vim *vm);
void PUSHACC2(vim *vm);
void PUSHACC3(vim *vm);
void PUSHACC4(vim *vm);
void PUSHACC5(vim *vm);
void PUSHACC6(vim *vm);
void PUSHACC7(vim *vm);
void PUSHACC(vim *vm);

void POP(vim *vm);
void ASSIGN(vim *vm);
void STOP(vim *vm);
void CHECK_SIGNALS(vim *vm);

// Branchements

void BRANCH(vim *vm);
void BRANCHIF(vim *vm);
void BRANCHIFNOT(vim *vm);

void SWITCH(vim *vm);

void BOOLNOT(vim *vm);
void EQ(vim *vm);
void NEQ(vim * vm);

// Entiers 

void CONST0(vim *vm);
void CONST1(vim *vm);
void CONST2(vim *vm);
void CONST3(vim *vm);
void CONSTINT(vim *vm);

void PUSHCONST0(vim *vm);
void PUSHCONST1(vim *vm);
void PUSHCONST2(vim *vm);
void PUSHCONST3(vim *vm);
void PUSHCONSTINT(vim *vm);

void NEGINT(vim *vm);
void ADDINT(vim *vm);
void SUBINT(vim *vm);
void MULINT(vim *vm);
void DIVINT(vim *vm);
void MODINT(vim *vm);
void ANDINT(vim *vm);
void ORINT(vim *vm);
void XORINT(vim *vm);
void LSLINT(vim *vm);
void LSRINT(vim *vm);
void ASRINT(vim *vm);

void LTINT(vim *vm);
void LEINT(vim *vm);
void GTINT(vim *vm);
void GEINT(vim *vm);

void ULTINT(vim *vm);
void UGEINT(vim *vm);

void OFFSETINT(vim *vm);
void ISINT(vim *vm);

void BEQ(vim *vm);
void BNEQ(vim *vm);
void BLTINT(vim *vm);
void BLEINT(vim *vm);
void BGTINT(vim *vm);
void BGEINT(vim *vm);
void BULTINT(vim *vm);
void BUGEINT(vim *vm);

// Primitives 

void C_CALL1(vim *vm);
void C_CALL2(vim *vm);
void C_CALL3(vim *vm);
void C_CALL4(vim *vm);
void C_CALL5(vim *vm);
void C_CALLN(vim *vm);

// Mémoire globale 

void GETGLOBAL(vim *vm);
void PUSHGETGLOBAL(vim *vm);
void SETGLOBAL(vim *vm);

// Création de blocs

void MAKEBLOCK(vim *vm);
void MAKEBLOCK1(vim *vm);
void MAKEBLOCK2(vim *vm);
void MAKEBLOCK3(vim *vm);

// Accès/écriture dans les blocs

void GETFIELD0(vim *vm);
void GETFIELD1(vim *vm);
void GETFIELD2(vim *vm);
void GETFIELD3(vim *vm);
void GETFIELD(vim *vm);

void SETFIELD0(vim *vm);
void SETFIELD1(vim *vm);
void SETFIELD2(vim *vm);
void SETFIELD3(vim *vm);
void SETFIELD(vim *vm);

void GETVECTITEM(vim *vm);
void SETVECTITEM(vim *vm);
void GETGLOBALFIELD(vim *vm);
void PUSHGETGLOBALFIELD(vim *vm);
void OFFSETREF(vim *vm);

// Atomes

void ATOM0(vim *vm);
void ATOM(vim *vm);
void PUSHATOM0(vim *vm);
void PUSHATOM(vim *vm);

#endif // INSTRUCTIONS_H