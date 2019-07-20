{
  u=v=p=q=1;
  for (k=1, 2000,
    [u,v] = [v,u+v];
    p *= v; q = lcm(q,v);
    if (k%50 == 0,
      print(k, " ", log(p)/log(q))
    )
  )
}
