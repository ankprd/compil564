
struct U { int x; int y; };

struct S { int a; struct U *u; int b; };

int main() {
  struct S *s;

  s = sbrk(sizeof(struct S));
  s->u = sbrk(sizeof(struct U));
  
  return 0;
}
