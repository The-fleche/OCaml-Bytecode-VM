#ifndef OBJETS_H
#define OBJETS_H

#include <stdio.h>
#include <stdlib.h>

#define Max 1000

typedef struct pile pile;


void affich_pile(pile *p);
void init_pile(pile *p);
int vacuite_test(pile *p);
long empile(pile *p, long val);
long depile(pile *p, int *erreur);

#endif // OBJETS_H