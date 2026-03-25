# Compilateur et options de compilation
# -g pour les débug info
CC = gcc -Wall -Wextra -g

# Nom de l'exécutable
EXEC = vm

# Fichiers objets
OBJ = main.o app.o instructions.o objets.o

# Première règle par convention : compilation de l'exécutable
all: $(EXEC)

# Édition des liens pour générer l'exécutable
$(EXEC): $(OBJ)
	$(CC) -o $@ $^

# Compilation séparée avec dépendances sur les headers uniquement

objets.o: objets.c objets.h
	$(CC) -c $< -o $@

instructions.o: instructions.c instructions.h objets.h
	$(CC) -c $< -o $@

app.o: app.c app.h instructions.h objets.h
	$(CC) -c $< -o $@

main.o: main.c app.h instructions.h objets.h
	$(CC) -c $< -o $@

