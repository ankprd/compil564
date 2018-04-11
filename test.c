int x, y;

int f(int y){
   while(y)
      ;
   return 2 * y;
}

int doubleIfSimplifiable(int x, int y){
   int z;
   z = 1;
   if(x == 1){
      if(y == 1)
         z = 0;
   }
   else{
      if(y == 1)
         z = 0;   
   }
   return z;
}

int main(){
   x =1;
   x == f(1);
   y = 2;
   return doubleIfSimplifiable(x, y);
}
