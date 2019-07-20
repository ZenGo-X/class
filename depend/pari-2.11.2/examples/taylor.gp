\\ adapted from an original idea by Ilya Zakharevich

\\ generate an RGB color triple from a "magnitude" between 0 and 255
\\ (low = close to a cold blue, high = close to a hot red).
\\ To generate simple colormaps.
rgb(mag) =
{ my(x = mag/255., B, G, R);
  B = min(max(4*(0.75-x),     0), 1);
  R = min(max(4*(x-0.25),     0), 1);
  G = min(max(4*abs(x-0.5)-1, 0), 1);
  return (floor([R, G, B]*255));
}
default(graphcolormap, concat(["white","black","blue"], vector(25,i,rgb(10*i))));
default(graphcolors, vector(25,i,i+2));

\\ plot Taylor polynomials of f,
\\ of index  first + i*step <= ordlim, for x in [xmin,xmax].
plot_taylor(f, xmin=-5, xmax=5, ordlim=16, first=1, step=1) =
{
  my(T,s,t,w,h,dw,dh,cw,ch,gh, extrasize = 0.6);
  my(Taylor_array);

  default(seriesprecision,ordlim+1);
  T = f('q);
  ordlim = (ordlim-first)\step + first;
  Taylor_array = vector(ordlim+1);
  forstep(i=ordlim+1, 1, -1,
    T += O('q^(1 + first + (i-1)*step));
    Taylor_array[i] = truncate(T)
  );

  t = plothsizes();
  w=floor(t[1]*0.9)-2; dw=floor(t[1]*0.05)+1; cw=t[5];
  h=floor(t[2]*0.9)-2; dh=floor(t[2]*0.05)+1; ch=t[6];

  plotinit(2, w+2*dw, h+2*dh);
  plotinit(3, w, floor(h/1.2));
  \\ few points (but Recursive!), to determine bounding box
  s = plotrecth(3, x=xmin,xmax, f(x),
                "Recursive|no_X_axis|no_Y_axis|no_Frame", 16);
  gh=s[4]-s[3];

  plotinit(3, w, h);
  plotscale(3, s[1], s[2], s[3]-gh*extrasize/2, s[4]+gh*extrasize/2);
  plotrecth(3, x=xmin,xmax, subst(Taylor_array, 'q, x), "no_Rescale");
  plotclip(3);
  plotcopy(3, 2, dw, dh);

  plotmove(2, floor(dw+w/2-15*cw), floor(dh/2));
  plotstring(2, "Multiple Taylor Approximations");
  plotdraw(2);
}

\p9
plot_taylor(sin)
plot_taylor(exp,-3,3)
plot_taylor(x->besselk(2,x), 1,5)
plot_taylor(x->1/(1+x^2), -1.2,1.2)
