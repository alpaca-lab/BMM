Read("cyclic.g");

# how to set up the coset table
MakeSetter:= function(M, N, null, one, mmm, params)
    local   basicVec,  vecUnderMat,  vecUnderWord,  rel,  inv,  gen,
            img,  setRow,  makeEdge;

    # scalar multiple of a basis vector
    basicVec:= function(k, val)
        local   vec;
        vec:= List([1..N], i-> null);
        vec[k]:= val;
        return vec;
    end;

    # vec * mat
    vecUnderMat:= function(vec, mat)
        local   img,  pos;
        img:= null * vec;
        for pos in [1..Length(vec)] do
            if vec[pos] <> null then
                if not IsBound(mat[pos]) then
                    return false;
                else
                    img:= img + vec[pos] * mat[pos];
                fi;
            fi;
        od;
        return img;
    end;

    # vec . word
    vecUnderWord:= function(vec, word)
        local   s;
        for s in word do
            vec:= vecUnderMat(vec, mmm[s mod M]);
            if vec = false then
                return vec;
            fi;
        od;
        return vec;
    end;

    ## how to make a new entry:

    # s = w
    rel:= function(i, s, w)
        return vecUnderWord(basicVec(i, one), w);
    end;

    # c[1] u' = u^2 - c[3] u - c[2]
    inv:= function(i, s, w)
        local   vec,  c,  sum,  j;
        vec:= basicVec(i, one);
        if s > 0 or -s > Length(params) then
            Error("did not expect s = ", s);
        fi;
        c:= params[-s];
        sum:= c[2] * vec;
        vec:= vecUnderWord(vec, [-s]);
        if vec = false then
            return false;
        fi;
        for j in [3..Length(c)] do
            sum:= sum + c[j] * vec;
            vec:= vecUnderWord(vec, [-s]);
            if vec = false then
                return false;
            fi;
        od;
        sum:= (-1) * sum + vec;
        return c[1]^-1 * sum;
    end;

    # u = c2 + c1 u' + c0 u'u'
    gen:= function(i, s, w)
        local   vec,  c,  sum,  j;
        vec:= basicVec(i, one);
        if s < 0 or s > Length(params) then
            Error("did not expect s = ", s);
        fi;
        c:= params[s];
        sum:= c[Length(c)] * vec;
        vec:= vecUnderWord(vec, [-s]);
        if vec = false then
            return false;
        fi;
        for j in Reversed([2..Length(c)-1]) do
            sum:= sum + c[j] * vec;
            vec:= vecUnderWord(vec, [-s]);
            if vec = false then
                return false;
            fi;
        od;
        sum:= sum + c[1] * vec;
        return sum;
    end;

    img:= function(i, s, w)
        return w;
    end;

    setRow:= function(i, s, w, fun)
        local   vec;
        Print(i, ".", s, " = \c");
        vec:= fun(i, s, w);
        if vec = false then
            Error("could not set row");
        fi;
        mmm[s mod M][i]:= vec;
        Print("done.\n");
    end;

    makeEdge:= function(source, target, s)
        setRow(source, s, basicVec(target, one), img);
        setRow(target, -s, basicVec(source, one), img);
    end;

    return rec(
      basicVec:= basicVec,
      vecUnderWord:= vecUnderWord,
      img:= img,
      rel:= rel,
      gen:= gen,
      inv:= inv,
      setRow:= setRow,
      makeEdge:= makeEdge
    );

end;

## how to compute the Gram matrix of the standard trace function
GramMatrix:= function(hecke)
    local   ts,  xs,  zs,  one,  basicVec,  vecUnderWord,  coeffsVec,
            c,  d,  e,  q,  bbb,  z,  zzz,  l,  i,  j,  zzc,  k,  cat,
            lb,  gram;

    ts:= hecke.ts;
    xs:= hecke.xs;
    zs:= hecke.zs;
    one:= hecke.one;
    basicVec:= hecke.basicVec;
    vecUnderWord:= hecke.vecUnderWord;

    # convert vec into list of coeffs
    coeffsVec:= x-> Concatenation(List(x, y-> y.list));

    c:= Length(ts); #  c: the size of W'
    d:= Length(xs); #  d: the size of the spanning tree: |W:W'| = de
    e:= Length(zs); #  e: the number of spanning trees: z^e = 1

    q:= []; # list of square blocks

    # all elements in one branch
    bbb:= List(Cartesian(xs, ts), x-> Concatenation(x{[2,1]}));

    z:= basicVec(1, one);
    zzz:= List(bbb, x-> vecUnderWord(z, x));

    # first row of blocks
    for l in [1..e] do
        q[l]:= [];
        for i in [1..Length(bbb)] do
            q[l][i]:= [];
            for j in [1..Length(bbb)] do
                q[l][i][j]:= vecUnderWord(zzz[i], bbb[j])[1].list[1];
            od;
        od;
        Print(TransposedMat(q[l]) = q[l], ";\c");
        zzz:= List(zzz, x-> vecUnderWord(x, zs[2]));
    od;

    # remaining blocks
    zzc:= List(zzz, coeffsVec);
    for k in e+[1..e-1] do
        cat:= Concatenation(q{[k-e..k-1]});
        q[k]:= zzc * cat;
        Print(".\c");
    od;
    Print("\n");

    # collect
    lb:= Length(bbb);
    #    gram:= [[]];
    gram:= List([1..e*lb], x-> 0*[1..e*lb]);
    for i in [1..e] do
        for j in [1..e] do
            gram{(i-1)*lb+[1..lb]}{(j-1)*lb+[1..lb]}:= q[i+j-1];
        od;
    od;

    return rec(gram:= gram, q:= q, zzc:= zzc);
end;
