# The bug in question is fixed in the GAP master branch
# (thus it will be fixed in GAP 4.12).
if CompareVersionNumbers( GAPInfo.Version, "4.12" ) then
  Info( InfoOD, 1,
        "the fix for FrobeniusCharacterValue is not needed anymore" );
fi;


###############################################################################
##
#F  FrobeniusCharacterValue( <value>, <p> )
##
##  Let $n$ be the conductor of $v$.
##  Let $k$ be the order of $p$ modulo $n$, that is, $\F_{p^k}$ is the
##  smallest field of characteristic $p$ containing $n$-th roots of unity.
##  Let $m$ be minimal with $v^{\ast p^m} = v$, that is, $\F_{p^m}$ is a
##  (not necessarily minimal) field containing the Frobenius character value
##  $\overline{v}$.
##
##  Let $C_k$ and $C_m$ be the Conway polynomials of degrees $k$ and $m$,
##  and $z = X + (C_k)$ in $\F_{p^k} = \F_p[X] / (C_k)$.
##  Then $\hat{y} = z^{\frac{p^k-1}{p^m-1}}$ may be identified with
##  $y = X + (C_m)$ in $\F_{p^m} = \F_p[X] / (C_m)$.
##
##  For $v = \sum_{i=1}^n a_i E(n)^i$, a representation of $\overline{v}$ in
##  $\F_{p^k}$ is $\sum_{i=1}^n \overline{a_i} z^{\frac{p^k-1}{n} i}$ where
##  $\overline{a_i}$ is the reduction of $a_i$ modulo $p$, viewed as
##  element of $\F_p$.
##
##  A representation of $\overline{v}$ in $\F_{p^m}$ can be found by
##  solving the linear equation system
##  $\overline{v} = \sum_{i=0}^{m-1} c_i \hat{y}^i$ over $\F_p$, which
##  gives us $\overline{v} = \sum{i=0}^{m-1} c_i y^i$ in $\F_{p^m}$.
##
BindGlobal( "FrobeniusCharacterValueFixed", function( value, p )
    local n,            # conductor of `value'
          k,            # degree of smallest field containing `n'-th roots
          size,         # `p^k'
          power,        # `( size - 1 ) / n'
          ffe,          # primitive `n'-th root in `GF( size )'
          cf,           # canonical basis of `CF(n)'
          m,            # degree of some field containing the result
          image,        # image of `value' under Galois conjugation
          primefield,   # `GF(p)'
          zero,         # zero of `primefield'
          one,          # identity of `primefield'
          conwaypol,    # coeffs. of the `k'-th Conway pol. in char. `p'
          x,            # coeffs. of an indeterminate
          y,
          lastvalue,
          fieldbase,
          i;

    # If <value> belongs to a <p>-singular element then return `fail'.
    n:= Conductor( value );
    if   n mod p = 0 then
      return fail;
    elif n = 1 then
      if DenominatorRat( value ) mod p = 0 then
        return fail;
      else
        return value * One( GF(p) );
      fi;
    elif IsCycInt( value / p ) then
      return Zero( GF(p) );
    fi;

    # Compute the size $p^k$ of the smallest finite field of characteristic
    # `p' that contains 'n'-th roots of unity.
    k:= OrderMod( p, n );
    size:= p^k;

    # The root `E(n)' is identified with the smallest primitive `n'-th
    # root in the finite field, that is, the `(size-1) / n'-th power of
    # the primitive root of the field
    # (which is given by the Conway polynomial).
    power:= ( size - 1 ) / n;

    if size <= MAXSIZE_GF_INTERNAL then

      # Use GAP's internal finite fields.
      # (Express the Brauer character value in terms of the Zumbroich basis
      # of the underlying cyclotomic field.)
      ffe:= PrimitiveRoot( GF( size ) ) ^ power;
      cf:= CanonicalBasis( CF( n ) );
      value:= Coefficients( cf, value ) *
                  List( ZumbroichBase( n, 1 ), exp -> ffe ^ exp );

    elif not IsCheapConwayPolynomial( p, k ) then

      # Give up if the required Conway polynomial is hard to compute.
      Info( InfoWarning, 1,
            "the Conway polynomial of degree ", k, " for p = ", p,
            " is not known" );
      return fail;

    else

      # Compute a finite field that contains the Frobenius character value.
      # An upper bound is given by the field of order $p^m$
      # where $m$ is the smallest number such that <value> is fixed
      # by the Galois automorphism that raises roots of unity
      # to the $p^m$-th power.
      m:= 1;
      image:= GaloisCyc( value, p );
      while image <> value do
        m:= m+1;
        image:= GaloisCyc( image, p );
      od;

      # Compute the representation of the Frobenius character value
      # in the field $\F_{p^k}$.
      primefield:= GF(p);
      zero:= Zero( primefield );
      one:= One( primefield );

      conwaypol:= ConwayPol( p, k ) * one;
      x:= [ zero, one ];
      value:= COEFFS_CYC( value ) * one;

      ConvertToVectorRepNC( conwaypol, p );
      ConvertToVectorRepNC( x, p );
      ConvertToVectorRepNC( value, p );

      value:= PowerModEvalPol( conwaypol,
                  value,
                  PowerModCoeffs( x, 2, power, conwaypol, k+1 ) );
      if IsEmpty( value ) then
        return zero;
      fi;
      PadCoeffs( value, k, zero );

      # Compute a $\F_p$-basis $(\hat{y}^i; 0\leq i\leq m-1)$ of
      # the subfield of $\F_{p^k}$ isomorphic with $\F_{p^m}$.
      y:= PowerModCoeffs( x, 2, (size - 1) / (p^m - 1), conwaypol, k+1 );

      lastvalue:= [ one ];
      fieldbase:= [ [ one ] ];
      PadCoeffs( fieldbase[1], k, zero );
      ConvertToVectorRepNC( fieldbase[1], p );

      for i in [ 2 .. m ] do
        lastvalue:= ProductCoeffs( y, lastvalue );
        ReduceCoeffs( lastvalue, conwaypol );
        ShrinkRowVector( lastvalue );
        PadCoeffs( lastvalue, k, zero );
        fieldbase[i]:= lastvalue;
        ConvertToVectorRepNC( fieldbase[i], p );
      od;

      value:= ValuePol( SolutionMatDestructive( fieldbase, value ),
                        Z( p, m ) );
    fi;

    # Return the Frobenius character value.
    return value;
end );


# The enhancement in question is in the GAP master branch
# (thus it will be fixed in GAP 4.12).
if CompareVersionNumbers( GAPInfo.Version, "4.12" ) then
  Info( InfoOD, 1,
        "the improvement for IndicatorOp is not needed anymore" );
fi;


###############################################################################
##
##  Improve the behaviour of 'Indicator' in characteristic 2.
##
InstallMethod( IndicatorOp,
    "for a Brauer character table and <n> = 2",
    [ IsBrauerTable, IsHomogeneousList, IsPosInt ], 10,
    function( modtbl, ibr, n )
    local ind, princ, i;

    if UnderlyingCharacteristic( modtbl ) <> 2 or ibr <> Irr( modtbl ) then
      TryNextMethod();
    fi;

    ind:= [];
    princ:= BlocksInfo( modtbl )[1].modchars;

    for i in [ 1 .. Length( ibr ) ] do
      if ibr[i] <> ComplexConjugate( ibr[i] ) then
        # Non-real characters have indicator 0.
        ind[i]:= 0;
      elif not i in princ then
        # Real characters outside the principal block have indicator 1.
        ind[i]:= 1;
      elif Set( ibr[i] ) = [ 1 ] then
        # The trivial character is defined to have indicator 1.
        ind[i]:= 1;
      else
        # Set 'Unknown()' for all other characters.
        ind[i]:= Unknown();
      fi;
    od;

    return ind;
    end );
#T Run a consistency check whether these criteria hold for the database,
#T and whether we can improve known values for the database.

