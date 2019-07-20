rgcd(a,b)=
{
  [a,b] = [abs(a), abs(b)];
  while (b > 0.01, [a,b] = [b,a%b]);
  a;
}

global(nf, km, m, clh, R, areg, re, res, mreg);

f(a,b, nf,v,ind)=
{ my(u, vreg);
  my(n = idealnorm(nf, a + b*variable(nf.pol)));
  my(mv = vectorv(#v));
  forprime (p=2, #ind,
    my (l = valuation(n,p));
    if (l,
      my(cp, j = ind[p]);
      n /= p^l; cp = v[j][2];
      while((a+b*cp)%p,
        j++; cp = v[j][2]
      );
      mv[j] = l
    )
  );
  if (n!=1, return);
  my (r1 = nf.sign[1]);

  /* found a relation */
  vreg = vectorv(#re,j,
    u = a+b*re[j];
    if (j<=r1, abs(u), norm(u))
  );
  mreg = concat(mreg, log(vreg));
  m = concat(m, mv);
  areg = concat(areg, a+b*t);
  print1("(" res++ ": " a "," b ")");
}

clareg(pol, plim=19, lima=50, extra=5)=
{ my(coreg,lireg,r1,ind,fa,co,a,b,mh,ms,mhs,mregh);

  nf=nfinit(pol); pol=nf.pol;
  re = nf.roots; r1=nf.sign[1];
  if (nf.index > 1, /* power basis <==> index = 1 */
    error("sorry, the case 'index>1' is not implemented")
  );
  printf("discriminant = %s, signature = %s\n", nf.disc, nf.sign);

  lireg = sum(i=1,2, nf.sign[i]); /* r1 + r2 */
  ind=vector(plim); v=[];
  forprime(p=2,plim,
    my (w = factormod(pol,p));
    my (e = w[,2]);
    my (find = 0);
    for(l=1,#e,
      fa = lift(w[l,1]);
      if (poldegree(fa) == 1,
        if (!find, find=1; ind[p]=#v+1);
        v = concat(v, [[p,-polcoeff(fa,0),e[l]]])
      )
    )
  );
  co = #v+extra;
  res=0; print("need ", co, " relations");
  areg=[]~; mreg = m = [;];
  a=1; b=1; f(0,1, nf,v,ind);
  while (res<co,
    if (gcd(a,b)==1,
      f(a,b, nf,v,ind); f(-a,b, nf,v,ind)
    );
    a++;
    if (a*b>lima, b++; a=1)
  );
  print(" ");
  mh=mathnf(m); ms=matsize(mh);
  if (ms[1]!=ms[2],
    print("not enough relations for class group: matrix size = ",ms);
    return
  );

  mhs = matsnf(mh,4);
  clh = prod(i=1,#mhs, mhs[i]);
  printf("class number = %s, class group = %s\n", clh, mhs);
  areg=Mat(areg); km=matkerint(m); mregh=mreg*km;
  if (lireg==1,
    R = 1
  ,
    coreg = #mregh;
    if (coreg < lireg-1,
      print("not enough relations for regulator: matsize = ", matsize(mregh));
      R = "(not given)";
    ,
      mreg1 = mregh[1 .. lireg-1, ];
      R = 0;
      for(j=lireg-1,coreg,
        a = matdet(mreg1[, j-lireg+2 .. j]);
        R = rgcd(a,R)
      )
    )
  );
  print("regulator = " R);
}

check(lim=200) =
{ my(r1,r2,pol,z,Res,fa);

  [r1,r2] = nf.sign;
  pol = nf.pol;
  z = 2^r1 * (2*Pi)^r2 / sqrt(abs(nf.disc)) / nfrootsof1(nf)[1];
  Res = 1.; \\ Res (Zeta_K,s=1) ~ z * h * R
  forprime (q=2,lim,
    fa = factormod(pol,q,1)[,1];
    Res *= (q-1)/q / prod(i=1, #fa, 1 - q^(-fa[i]))
  );
  z * clh * R / Res;
}

fu() = vector(#km, k, factorback(concat(areg, km[,k])));
