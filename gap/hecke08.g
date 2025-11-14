#############################################################################
##
##  H(G8)
##
Read("support.g");

HeckeCRG08:= function(params)
    local   C4Elt,  M,  N,  mmm,  c0,  c1,  c2,  c3,  null,  one,
            setter,  basicVec,  vecUnderWord,  img,  rel,  gen,  inv,
            setRow,  makeEdge,  u,  u1,  k,  s,  t,  z,  zs,  ts,  xs;

    # constructor
    C4Elt:= MakeC4Elts(params[1]);

    # matrices.  -1 mod 7 = 6 and -2 mod 7 = 5
    M:= 7;  N:= 24;
    mmm:= List([1..M-1], x-> []);

    # name some C3Elts
    c0:= params[1][1];  c1:= params[1][2];  c2:= params[1][3];   c3:= params[1][4];
    null:= C4Elt([0*c0, 0*c0, 0*c0, 0*c0]);    # 0
    one:= C4Elt([c0^0, 0*c0, 0*c0, 0*c0]);     # 1

    setter:= MakeSetter(M, N, null, one, mmm, params{[1,1]});
    basicVec:= setter.basicVec;
    vecUnderWord:= setter.vecUnderWord;
    img:= setter.img;  rel:= setter.rel;
    gen:= setter.gen;  inv:= setter.inv;
    setRow:= setter.setRow;
    makeEdge:= setter.makeEdge;

    # subgroup table
    u:= C4Elt([0*c0, c0^0, 0*c0, 0*c0]);        # u
    u1:= c0^-1 * C4Elt([-c1, -c2, -c3, c0^0]);  # u'
    for k in 6*[0..3] do
        setRow(k+1, 1, basicVec(k+1, u), img);
        setRow(k+1, -1, basicVec(k+1, u1), img);
        setRow(k+4, 2, basicVec(k+4, u), img);
        setRow(k+4, -2, basicVec(k+4, u1), img);
    od;

    # spanning tree(s)
    for k in 6*[0..3] do
        makeEdge(k+1, k+2, 2);
        makeEdge(k+2, k+3, 2);
        makeEdge(k+4, k+5, 1);
        makeEdge(k+5, k+6, 1);
    od;

    # w*
    for k in [0..20] do
        makeEdge(k+1, k+4, 3);
    od;

    s:= 1;  t:= 2;
    for k in 3*[0..6] do
        setRow(k+2, s, [ -t, -s, 3 ], rel);
        setRow(k+2, -s, 0, inv);
        setRow(k+4, -s, [ -3, s, t ], rel);
        setRow(k+6, s, 0, gen);
        s:= 3 - s;  t:= 3 - t;
    od;

    s:= 1;  t:= 2;
    for k in 3*[0..5] do
        setRow(k+3, s, [ -t, -s, 3 ], rel);
        s:= 3 - s;  t:= 3 - t;
    od;

    setRow(3, -1, 0, inv);
    setRow(6, -2, 0, inv);

    s:= 1;  t:= 2;
    for k in 3*[0..4] do
        setRow(k+9, -s, [-3, s, t], rel);
        s:= 3 - s;  t:= 3 - t;
    od;

    setRow(21, 1, 0, gen);

    setRow(3, 2, [ -1, -2, 3 ], rel);
    setRow(1, -2, 0, inv);
    setRow(23, -2, [ -3, 2, 1 ], rel);
    setRow(23, 2, 0, gen);
    setRow(24, -2, [ -3, 2, 1 ], rel);
    setRow(24, 2, 0, gen);

    for k in [22..24] do
        setRow(k, 3, [ 1, 2, 1 ], rel);
    od;

    for k in [1..3] do
        setRow(k, -3, -[ 1, 2, 1 ], rel);
    od;

    z:= [1,2,1,2,1,2];
    zs:= [[]];
    for k in [2..4] do
        zs[k]:= Concatenation(zs[k-1], z);
    od;

    ts:= [[], [1], [1,1], [1,1,1]];
    xs:= [[], [2], [2,2], [2,1,2], [2,1,2,1], [2,1,2,1,1]];

    return rec(
      matgens := mmm,
      params:= params,
      zs:= zs,  ts:= ts,  xs:= xs,
      one:= one,
      basicVec:= basicVec,
      vecUnderWord:= vecUnderWord,
      words:= List(Cartesian(zs, xs), Concatenation) # coset reps
    );

end;

GenericHeckeCRG08:= function()
    local   c0,  c1,  c2,  c3;

    ## indeterminates
    c0:= Mvp("c0");  c1:= Mvp("c1");  c2:= Mvp("c2");  c3:= Mvp("c3");

    return HeckeCRG08([[c0, c1, c2, c3]]);
end;

TestGenericHeckeCRG08:= function()
    local   hecke,  mmm,  M,  params,  c0,  c1,  c2,  c3,  test,  m12,
            m2;

    hecke:= GenericHeckeCRG08();

    mmm:= hecke.matgens;
    M:= Length(mmm) + 1;
    params:= hecke.params;
    c0:= params[1][1];  c1:= params[1][2];  c2:= params[1][3];  c3:= params[1][4];

    test:= rec(relations:= [], powers:= []);

    Print("testing relation ... \c");
    m12:= mmm[1] * mmm[2];
    test.relations[1]:= mmm[2] * m12 = m12 * mmm[1];
    Print(test.relations[1], "\n");

    Print("testing power ... \c");
    m2:= mmm[1] * mmm[1];
    test.powers[1]:=
      m2 * m2  = c3 * m2 * mmm[1] + c2 * m2 + c1 * mmm[1] + c0 * mmm[1] * mmm[-1 mod M];
    Print(test.powers[1], "\n");

    Print("testing power ... \c");
    m2:= mmm[2] * mmm[2];
    test.powers[2]:=
      m2 * m2  = c3 * m2 * mmm[2] + c2 * m2 + c1 * mmm[2] + c0 * mmm[2] * mmm[-2 mod M];
    Print(test.powers[2], "\n");

    return test;
end;

test:= function()
    local   hecke,  gram,  det;
    hecke:= GenericHeckeCRG08();
    gram:= GramMatrix(hecke);
    det:= DeterminantMat(gram.gram);
    Print("det = ", det, "\n");
end;
