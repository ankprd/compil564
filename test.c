// un exemple de fichier mini-C
// à modifier au fur et à mesure des tests
//
// la commande 'make' recompile mini-c (si nécessaire)
// et le lance sur ce fichier

struct S
{
	int a;
	int b;
	struct S *p;
};

int main() {
  return sizeof(struct S);
}