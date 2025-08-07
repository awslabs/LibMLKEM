#include <cpucycles.h>
#include <stdint.h>
#include <stdalign.h>
#include <stdio.h>

#include "poly.h"

void setp(mlk_poly *p, int16_t x)
{
   for (size_t i = 0; i < MLKEM_N; i++)
   {
      p->coeffs[i] = x;
   }
}

void pp(mlk_poly *p)
{
   for (size_t i = 0; i < MLKEM_N; i++)
   {
       printf("%d ", p->coeffs[i]);
   }
   printf("\n");
}

void pp2(mlk_poly *p)
{
   for (size_t i = 0; i < MLKEM_N; i++)
   {
      if (p->coeffs[i] < 0)
      {
 	 printf("%d ", (uint32_t) p->coeffs[i] + 3329);
      } else
      {
         printf("%d ", p->coeffs[i]);
      }
   }
   printf("\n");
}


int main()
{
   mlk_poly p1;

   long long count1 = cpucycles();
   long long count2;
   long long e;

   printf ("Testing...\n");
   setp (&p1, 3);
   pp(&p1);

   count1 = cpucycles();
//   for (int i = 0; i < 1000; i++)
//   {
      mlk_poly_ntt(&p1);
      mlk_poly_reduce(&p1);
//   }
   count2 = cpucycles();
   e = count2 - count1;

   printf ("Result...\n");
   pp(&p1);
   printf ("Result normalized...\n");
   pp2(&p1);

   printf ("poly_ntt() cycles = %lld\n", e);

   return 0;
}
