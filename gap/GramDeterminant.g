#############################################################################
##  
##  GramDeterminant.g                                       Frank Lübeck
##  
##  Some utilities for Specht modules of symmetric groups.
##  
##  If la is a partition of n then a basis of the Specht module L(la) of S_n
##  is parameterized by standard tableaux of shape la. 
##  
##  The Gram matrix with respect to this basis has a determinant that can
##  be computed combinatorically using a formula of Jantzen and Schaper
##  (see 5.33 in book of Andrew Mathas).
##  
##  The factorized determinant of the Gram matrix can be computed with 
##  GramDeterminant.
##  
##  Examples:
##  gap> la := [4,2,1];
##  [ 4, 2, 1 ]
##  gap> DualPartition(la);
##  [ 3, 2, 1, 1 ]
##  gap> DimensionSpecht(la);
##  35
##  gap> GramDeterminant(la);
##  [ [ 2, 43 ], [ 3, 28 ] ]
##  

DualPartition := function(lambda)
  local res, k, j;
  res := [];
  k := Length(lambda);
  for j in [1..lambda[1]] do
    if j <= lambda[k] then
      res[j] := k;
    else
      k := k-1;
      while j > lambda[k] do
        k := k-1;
      od;
      res[j] := k;
    fi;
  od;
  return res;
end;

# from Mathas' book, 5.33 (partitions transposed)
SchaperDecomposition := function(lambda, p)
  local n, sgn, mu, hooklens, mux, lax, bmu, res, nups, b, a, d, beta, i, j, k;
  
  n := Sum(lambda);
  sgn := (-1)^Int(n/2);
  mu := DualPartition(lambda);
  
  # hook lengths, col-wise
  hooklens := [];
  mux := mu-[0..Length(mu)-1];
  lax := lambda-[1..Length(lambda)];
  for i in [1..Length(mu)] do
    Add(hooklens, mux[i] + lax{[1..mu[i]]});
  od;

  # beta numbers for mu, see 5.20
  bmu := ShallowCopy(lambda);
  for i in [Length(bmu)+1..n] do
    Add(bmu, 0);
  od;
  bmu := bmu + [n-1,n-2..0];

  # collect coeffs in first list and partitions in second, formula 5.33
  res := [[],[]];
  for i in [1..Length(mu)] do
    # nu_p(h_x,i)
    nups := [];
    for a in hooklens[i] do
      b := 0;
      while a mod p = 0 do
        b := b+1;
        a := a/p;
      od;
      Add(nups, b);
    od;
    for j in [1..mu[i]-1] do
      for k in [j+1..mu[i]] do
        d := nups[j] - nups[k];
        # only term if resulting list gives beta numbers of a partition, 
        # see before 5.32
        if d <> 0 then
          a := bmu[j] + hooklens[i][k];
          if not a in bmu then
            beta := ShallowCopy(bmu);
            beta[j] := a;
            a := beta[k] - hooklens[i][k];
            if a >= 0 and not a in beta then
              beta[k] := a;
              b := SignPerm(Sortex(beta))*sgn;
              Add(res[1], b*d);
              beta := beta{[n,n-1..1]}-[n-1,n-2..0];
              ShrinkRowVector(beta);
              # note again, that partitions are transposed here
              Add(res[2], beta);
            fi;
          fi;
        fi;
      od;
    od;
  od;
  return res;
end;

# the hook formula
DimensionSpecht := function(mu)
  local la, d, f, m, mux, lax, i, j;
  la := DualPartition(mu);
  d := 1;
  f := 1;
  m := 1;
  mux := mu-[0..Length(mu)-1];
  lax := la-[1..Length(la)];
  for i in [1..Length(mu)] do
    for j in [1..mu[i]] do
      d := d * (mux[i] + lax[j]);
      f := f * m;
      m := m + 1;
    od;
  od;
  return f / d;
end;

# determinant of Gram matrix for Specht module S^mu, in factorized collected  
# form 
GramDeterminant := function(mu)
  local n, det, s, p;
  n := Sum(mu);
  det := [];
  for p in [2..n] do
    if IsPrimeInt(p) then
      s := SchaperDecomposition(mu, p);
      if Length(s[1]) > 0 then
        Add(det,[p, s[1] * List(s[2], DimensionSpecht)]);
      fi;
    fi;
  od;
  return det;
end;


