// un exemple de fichier mini-C
// à modifier au fur et à mesure des tests
//
// la commande 'make' recompile mini-c (si nécessaire)
// et le lance sur ce fichier


struct ABR {
  int valeur;
  struct ABR *gauche, *droite;
};

int main() {
  struct ABR *a;
  struct ABR *b;
  struct ABR *c;
  a->gauche = b;
  b->gauche = c;
  a->gauche->gauche->gauche = a;
  return 0; 
}
