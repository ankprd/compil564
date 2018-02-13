// un exemple de fichier mini-C
// à modifier au fur et à mesure des tests
//
// la commande 'make' recompile mini-c (si nécessaire)
// et le lance sur ce fichier

struct S
{
	int a;
	struct S *p;
};

int main() {
  struct S *u;
  u->p->a = 12;
}