/*int many(int a, int b, int c, int d, int e, int f, int g, int h, int i, int j) {
    many(b, c, d, e, f, g, h, i, j, a);
  return 0;
}
int main() {
  many(1, 2, 3, 4, 5, 6, 7, 8, 9, 10);
  return 0;
}
*/

int main() {
  putchar(65 + (1 || 1)); // 66, pas 67 !
  putchar(65 + (0 || 2)); // 66, pas 67 !
  putchar(65 + (1 || 0));
  putchar(65 + (0 || 0));
  putchar(10);
  return 0;
}
