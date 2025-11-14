#############################################################################
##
##  H(G10)
##

CHECK_REL:= false;  # set this to `true` to have relations checked

## indeterminates
a:= Mvp("a");
b:= Mvp("b");
c:= Mvp("c");
d:= Mvp("d");
e:= Mvp("e");
f:= Mvp("f");
g:= Mvp("g");

#g:= 3;
f:= 11*g;  e:= 17*g;
d:= 5*g;  c:= 13*g;  b:= 19*g;  a:= 23*g;


#  a C4 elt is a quadruple of polynomials in a, b, c, d
#  corresponding to the coefficients of a linear combination
#  of s^0, s^1, s^2 and s^3
#  addition is componentwise
#  multiplication distributive, where s^4 = a s^3 + b s^2 + c s + d
#  inversion:  d s' = s^3 - a s^2 - b s - c.

# operations record
C4EltOps:= OperationsRecord("C4EltsOps");

# constructor
C4Elt:= function(list)
    return rec(list:= list, isC4Elt:= true, operations:= C4EltOps);
end;

# type check
IsC4Elt:= function(obj)
    return IsRec(obj) and IsBound(obj.isC4Elt) and obj.isC4Elt = true;
end;

# how to print
C4EltOps.Print:= function(self)
    #    Print("C4Elt(", self.list, ")");
    if self.list = 0*self.list then
        Print(self.list[1]);
    else
        if self.list[1] <> 0 * self.list[1] then
            Print(self.list[1], "");
        fi;
        if self.list[2] <> 0 * self.list[2] then
            Print("+(", self.list[2], ")*s");
        fi;
        if self.list[3] <> 0 * self.list[3] then
            Print("+(", self.list[3], ")*s^2");
        fi;
        if self.list[4] <> 0 * self.list[4] then
            Print("+(", self.list[4], ")*s^3");
        fi;
    fi;
end;

# sum
C4EltOps.\+:= function(l, r)
    return C4Elt(l.list + r.list);
end;

# product
C4EltOps.\*:= function(l, r)
    local   p,  i,  j;

    if not IsC4Elt(l) then
        return C4Elt(l * r.list);
    fi;

    if IsList(r) then
        return List(r, a-> l * a);
    fi;

    p:= 0 * a *  [2..Sum(List([l, r]), x-> Length(x.list))];
    for i in [0..Length(l.list)-1] do
        for j in [0..Length(r.list)-1] do
            p[i+j+1]:= p[i+j+1] + l.list[i+1] * r.list[j+1];
        od;
    od;
    for l in Reversed([5..Length(p)]) do   # s^4 = a s^3 + b s^2 + c s + d
        p[l-1]:= p[l-1] + a * p[l];
        p[l-2]:= p[l-2] + b * p[l];
        p[l-3]:= p[l-3] + c * p[l];
        p[l-4]:= p[l-4] + d * p[l];
        Unbind(p[l]);
    od;
    return C4Elt(p);
end;

# matrices.  -1 mod 9 = 8 and -2 mod 9 = 7
M:= 9;  N:= 72;
mmm:= List([1..M-1], x-> []);

# name some C4Elts
null:= C4Elt([0*a,0*a,0*a,0*a]);
one:= C4Elt([a^0,0*a,0*a,0*a]);
u:= C4Elt([0*a,a^0,0*a,0*a]);   # s
u1:= d^-1 * C4Elt([-c,-b,-a,a^0]);  # s'

basicVec:= function(k, val)
    local   vec;
    vec:= List([1..N], i-> null);
    vec[k]:= val;
    return vec;
end;

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

# d u' = u^3 - a u^2 - b u - c
# g t' = t^2 - e t - f
inv:= function(i, s, w)
    local   vec,  sum;
    vec:= basicVec(i, one);
    if s = -1 then
        sum:= c * vec;
        vec:= vecUnderWord(vec, [-s]);
        if vec = false then
            return false;
        fi;
        sum:= sum + b * vec;
        vec:= vecUnderWord(vec, [-s]);
        if vec = false then
            return false;
        fi;
        sum:= sum + a * vec;
        vec:= vecUnderWord(vec, [-s]);
        if vec = false then
            return false;
        fi;
        sum:= (-1) * sum + vec;
        return d^-1 * sum;
    elif s = -2 then
        sum:= f * vec;
        vec:= vecUnderWord(vec, [-s]);
        if vec = false then
            return false;
        fi;
        sum:= sum + e * vec;
        vec:= vecUnderWord(vec, [-s]);
        if vec = false then
            return false;
        fi;
        sum:= (-1) * sum + vec;
        return g^-1 * sum;
    else
        Error("did not expect s = ", s);
    fi;
end;

# u = a + b u' + c u'u' + d u'u'u'
# t = e + f t' + g t't'
gen:= function(i, s, w)
    local   vec,  sum;
    vec:= basicVec(i, one);
    if s = 1 then
        sum:= a * vec;
        vec:= vecUnderWord(vec, [-s]);
        if vec = false then
            return false;
        fi;
        sum:= sum + b * vec;
        vec:= vecUnderWord(vec, [-s]);
        if vec = false then
            return false;
        fi;
        sum:= sum + c * vec;
        vec:= vecUnderWord(vec, [-s]);
        if vec = false then
            return false;
        fi;
        sum:= sum + d * vec;
        return sum;
    elif s = 2 then
        sum:= e * vec;
        vec:= vecUnderWord(vec, [-s]);
        if vec = false then
            return false;
        fi;
        sum:= sum + f * vec;
        vec:= vecUnderWord(vec, [-s]);
        if vec = false then
            return false;
        fi;
        sum:= sum + g * vec;
        return sum;
    else
        Error("did not expect s = ", s);
    fi;
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


# subgroup table
for k in 6*[0..11] do
    setRow(k+1, 1, basicVec(k+1, u), img);
    setRow(k+1, -1, basicVec(k+1, u1), img);
od;

# spanning tree
tree:= [
  [1,4,3], [4,2,-2], [2,5,3], [5,3,-2], [3,6,3],
];

for k in 6*[0..11] do
    for xys in tree do
        x:= xys[1];
        y:= xys[2];
        s:= xys[3];
        makeEdge(k+x, k+y, s);
    od;
od;

# z*
for k in [0..65] do
    makeEdge(k+1, k+7, 4);
od;

for k in 6*[0..11] do
    setRow(k+4, 1, [ -2, 3 ], rel);
    setRow(k+5, 1, [ -2, 3 ], rel);
    setRow(k+5, -1, [ -3, 2 ], rel);
    setRow(k+6, -1, [ -3, 2 ], rel);
od;

for k in 6*[0..10] do
    setRow(k+4, 3, [ -3, 4 ], rel);
    setRow(k+5, 3, [ -3, 4 ], rel);
    setRow(k+6, 3, [ -3, 4 ], rel);
    setRow(k+7, -3, [ 3, -4 ], rel);
    setRow(k+8, -3, [ 3, -4 ], rel);
    setRow(k+9, -3, [ 3, -4 ], rel);
od;

for k in 6*[0..10] do
    setRow(k+4, 2, [ 3, -1 ], rel);
    setRow(k+7, -2, [ 1, -3 ], rel);
    setRow(k+7, 2, 0, gen);
    setRow(k+2, -2, 0, inv);
od;

for k in 6*[0..10] do
    setRow(k+2, 1, [ -2, 3 ], rel);
    setRow(k+10, -1, [ -3, 2 ], rel);
    setRow(k+12, 1, 0, gen);
od;

for k in 6*[0..9] do
    setRow(k+8, -1, 0, inv);
od;

for k in 6*[0..9] do
    setRow(k+5, 2, [ 3, -1 ], rel);
    setRow(k+18, -2, [ 1, -3 ], rel);
    setRow(k+3, -2, 0, inv);
od;

for k in 6*[0..7] do
    setRow(k+18, 2, 0, gen);
od;

for k in 6*[0..8] do
    setRow(k+3, 1, [ -2, 3 ], rel);
od;

for k in 6*[0..7] do
    setRow(k+21, -1, [ -3, 2 ], rel);
od;

setRow(9, -1, 0, inv);
setRow(15, -1, 0, inv);
setRow(57, 1, 0, gen);
setRow(63, 1, 0, gen);

setRow(6, 2, [ 3, -1 ], rel);
setRow(12, 2, [ 3, -1 ], rel);
setRow(63, -2, [ 1, -3 ], rel);

setRow(65, 2, 0, gen);
setRow(66, 2, 0, gen);
setRow(6, -2, 0, inv);
setRow(12, -2, 0, inv);

setRow(6, 1, [ -2, 3 ], rel);
setRow(68, -1, [ -3, 2 ], rel);
setRow(69, -1, [ -3, 2 ], rel);

setRow(2, -1, 0, inv);
setRow(4, -1, 0, inv);

setRow(1, 2, [ 3, -1 ], rel);
setRow(1, -2, 0, inv);

setRow(1, -3, [ -1, -2 ], rel);

setRow(4, -4, [ -3, -3 ], rel);

setRow(3, -1, [ 3, 2, -1, -2, -3 ], rel);

setRow(68, 1, 0, gen);
setRow(69, 1, 0, gen);

setRow(2, -3, [ 2, -4, 1 ], rel);
setRow(3, -3, [ 3, -2, -3, -1 ], rel);

setRow(5, -4, [ -1, -4, 1 ], rel);
setRow(6, -4, [ 1, -4, -1 ], rel);

setRow(68, -2, [ 1, -3 ], rel);
setRow(69, -2, [ 1, -3 ], rel);

setRow(1, -4, [-3, -3], rel);
setRow(2, -4, [-3, -3], rel);
setRow(3, -4, [-3, -3], rel);

setRow(70, 2, 0, gen);
setRow(71, 2, 0, gen);
setRow(72, 2, 0, gen);

setRow(70, 3, [ 2, 1 ], rel);
setRow(71, 3, [ 2, 1 ], rel);
setRow(72, 3, [ 2, 1 ], rel);

for k in [67..72] do
    setRow(k, 4, [ 3, 3 ], rel);
od;

# test
if CHECK_REL then
    Print("testing relations ... \c");
    m12:= mmm[1] * mmm[2];
    Print(mmm[3] = mmm[2] * mmm[1], "\n");
    Print(m12 * m12 = mmm[3] * mmm[3], "\n");
    Print("testing power ... \c");
    m1:= mmm[1] * mmm[1];
    Print(m1 * m1 = a * m1 * mmm[1] + b * m1 + c * mmm[1] + d * mmm[1] * mmm[-1 mod M], "\n");
    Print("testing power ... \c");
    m2:= mmm[2] * mmm[2];
    Print(m2 * mmm[2] = e * m2 + f * mmm[2] + g * mmm[2] * mmm[-2 mod M], "\n");
fi;
