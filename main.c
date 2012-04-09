int if1, if2;

char *f(char *p) {
   char *q;
   if (if1) q = "bar";
   else q = p;
   return q;
}

void main(void) {
  char *r, *s, *p, **t, **q;
  p = "foo";
  if (if2) r = f(p);
  else r = p;
  s = r;
  r = "test";
  q = &r;
  t = q;
  *t = s;
}