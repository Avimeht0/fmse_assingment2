#include<vcc.h>
#include<limits.h>
/*
//Q1
unsigned mult (unsigned n, unsigned m)
_(requires n <= 100 && m <= 100)
_(ensures \result == n*m) {
  unsigned a = 0;
  unsigned x = 0;
  while (x < m) 
  _(invariant a == n*x)
  //_(invariant a==n*x && n*x<=UNIT_MAX)
  {
    a = a + n;
    x = x + 1;
  }
  return a;

}

  int main() {
    unsigned res=mult(30,45)
    return 0;
}*/

/*
//Q2
int max3(int x, int y, int z)
    _(requires \true) // Specification: function can be called under any condition
    _(ensures \result >= x && \result >= y && \result >= z) // Specification: result is greater than or equal to all input values
    _(ensures \result == x || \result == y || \result == z) // Specification: result is one of the input values
{
    if (x <= y)
     if (y <= z)
      return z;
    else
      return y;
  else
    if (x <= z)
      return z;
    else
      return x;
}

int main() {
    int res = max3(10, 3, 5);
    return 0;
}

*/
//q3

#include <limits.h> // for UINT_MAX

void sumcopy(unsigned A[10], unsigned B[10], unsigned C[10])
  _(requires \forall unsigned k; k < 10 ==> A[k] < 100)
  _(requires \forall unsigned k; k < 10 ==> B[k] < 100)
  _(ensures \forall unsigned k; (0 <= k && k < 10) ==> C[k] >= A[k])
{
    unsigned i;
    for (i = 0; i < 10; i++)
      _(invariant \forall unsigned j; (0 <= j && j < i) ==> C[j] >= A[j])
      _(invariant \forall unsigned k; k < i ==> (UINT_MAX - B[k] >= A[k])) // Ensure no overflow
    {
        C[i] = A[i] + B[i];
    }
}


int main()
{
  unsigned A[10] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
  unsigned B[10] = {10, 9, 8, 7, 6, 5, 4, 3, 2, 1};
  unsigned C[10];
  sumcopy(A,B,C);
  return 0;
}


/*
//q4
void main(){
  unsigned res = sum(10);
  _(assert res >= 10)
}

unsigned sum (unsigned n)
_(requires n <= 100)
_(ensures \result==(n*(n+1))/2)
{
  if (n == 0)
    return 0;
  else
    return (n + sum(n-1));
}
/*
//q5
unsigned count;
unsigned lo, mid, hi;

void init()
_(ensures count==0 && lo==0 && mid==0 &&  hi==0)
{
  count = 0;
  lo = 0;
  mid = 0;
  hi = 0;
}

void inc()
  // Precondition for inc
_(requires count<65535)		//so that atleast 1 can be added
_(requires (hi < 255 || mid < 255 || lo < 255))
_(ensures count==count+1)
_(ensures count==hi*65535+mid *256+lo)
{
  if (lo < 255)
    lo = lo + 1;
  else if (mid < 255) {
    lo = 0;
    mid = mid + 1;
  }
  else {
    lo = 0;
    mid = 0;
    hi = hi + 1;
  }
//count=hi*65535+mid *256+lo;
}

void dec() 
_(requires count>0)
_(requires (hi >0 || mid >0 || lo >0))
_(ensures count=count-1)
_(ensures count==hi*65535+mid *256+lo)
{ 
  if(lo > 0)
    lo=lo-1;
  else if(mid > 0){
    mid=mid-1;
    lo=255
  };
  else {
    hi=hi-1;
    mid=255;
    lo=255;
  }
//count=hi*65535+mid *256+lo;
}


*/