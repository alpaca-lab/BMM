#############################################################################
##
##  H(G15)
##

CHECK_REL:= false;  # set this to `true` to have relations checked

## indeterminates
a0:= Mvp("a0");  a1:= Mvp("a1");
b0:= Mvp("b0");  b1:= Mvp("b1");  b2:= Mvp("b2");
c0:= Mvp("c0");  c1:= Mvp("c1");  c2:= Mvp("c2");  c3:= Mvp("c3");

# a0:= a0^0;  a1:= 0*a0;
# b0:= b0^0;  b1:= 0*b1;  b2:= 0*b2;
# c0:= c0^0;  c1:= 0*c1;  c2:= 0*c2;  c3:= 0*c3;
c1:= 0*c1;  c3:= 0*c3;

# a0:= 2 * c0;  a1:= 7 * c0;
# b0:= 3 * c0;  b1:= 11 * c0;  b2:= 17 * c0;
# c0:= 5 * a0;  c1:= 13 * a0;  c2:= 19 * a0;  c3:= 23 * a0;

#  a C4 elt is a quadruple of polynomials in c3, c2, c1, c0
#  corresponding to the coefficients of a linear combination
#  of s^0, s^1, s^2 and s^3
#  addition is componentwise
#  multiplication distributive, where s^4 = c3 s^3 + c2 s^2 + c1 s + c0
#  inversion:  c0 s' = s^3 - c3 s^2 - c2 s - c1.

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
    local   o,  p,  i,  j;

    if not IsC4Elt(l) then
        return C4Elt(l * r.list);
    fi;

    if IsList(r) then
        return List(r, a-> l * a);
    fi;

    o:= 0 * c0;
    p:= o * [2..Length(l.list)+Length(r.list)];
    for i in [0..Length(l.list)-1] do
        if l.list[i+1] <> o then
            for j in [0..Length(r.list)-1] do
                if r.list[j+1] <> o then
                    p[i+j+1]:= p[i+j+1] + l.list[i+1] * r.list[j+1];
                fi;
            od;
        fi;
    od;
    for l in Reversed([5..Length(p)]) do   # s^4 = c3 s^3 + c2 s^2 + c1 s + c0
        if p[l] <> o then
            p[l-1]:= p[l-1] + c3 * p[l];
            p[l-2]:= p[l-2] + c2 * p[l];
            p[l-3]:= p[l-3] + c1 * p[l];
            p[l-4]:= p[l-4] + c0 * p[l];
        fi;
        Unbind(p[l]);
    od;
    return C4Elt(p);
end;

# matrices.
M:= 9;  N:= 144;
mmm:= List([1..M-1], x-> []);

# name some C4Elts
null:= C4Elt([0,0,0,0]*c0);
one:= C4Elt([1,0,0,0]*c0^0);
u:= C4Elt([0,1,0,0]*c0^0);        # u
u1:= C4Elt([-c1,-c2,-c3,1]/c0);   # u'

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
#                Print("?? ", pos);
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
#            Print(" of ", s, " missing??\n");
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

# a0 s' = s - a1
# b0 t' = t^2 - b2 t - b1
# c0 u' = u^3 - c3 u^2 - c2 u - c1
inv:= function(i, s, w)
    local   vec,  sum;
    vec:= basicVec(i, one);
    if s = -1 then
        sum:= a1 * vec;
        vec:= vecUnderWord(vec, [-s]);
        if vec = false then
            return false;
        fi;
        sum:= (-1) * sum + vec;
        return a0^-1 * sum;
    elif s = -2 then
        sum:= b1 * vec;
        vec:= vecUnderWord(vec, [-s]);
        if vec = false then
            return false;
        fi;
        sum:= sum + b2 * vec;
        vec:= vecUnderWord(vec, [-s]);
        if vec = false then
            return false;
        fi;
        sum:= (-1) * sum + vec;
        return b0^-1 * sum;
    elif s = -3 then
        sum:= c1 * vec;
        vec:= vecUnderWord(vec, [-s]);
        if vec = false then
            return false;
        fi;
        sum:= sum + c2 * vec;
        vec:= vecUnderWord(vec, [-s]);
        if vec = false then
            return false;
        fi;
        sum:= sum + c3 * vec;
        vec:= vecUnderWord(vec, [-s]);
        if vec = false then
            return false;
        fi;
        sum:= (-1) * sum + vec;
        return c0^-1 * sum;
    else
        Error("did not expect s = ", s);
    fi;
end;

# s = a1 + a0 s'
# t = b2 + b1 t' + b0 t't'
# u = c3 + c2 u' + c1 u'u' + c0 u'u'u'
gen:= function(i, s, w)
    local   vec,  sum;
    vec:= basicVec(i, one);
    if s = 1 then
        sum:= a1 * vec;
        vec:= vecUnderWord(vec, [-s]);
        if vec = false then
            return false;
        fi;
        sum:= sum + a0 * vec;
        return sum;
    elif s = 2 then
        sum:= b2 * vec;
        vec:= vecUnderWord(vec, [-s]);
        if vec = false then
            return false;
        fi;
        sum:= sum + b1 * vec;
        vec:= vecUnderWord(vec, [-s]);
        if vec = false then
            return false;
        fi;
        sum:= sum + b0 * vec;
        return sum;
    elif s = 3 then
        sum:= c3 * vec;
        vec:= vecUnderWord(vec, [-s]);
        if vec = false then
            return false;
        fi;
        sum:= sum + c2 * vec;
        vec:= vecUnderWord(vec, [-s]);
        if vec = false then
            return false;
        fi;
        sum:= sum + c1 * vec;
        vec:= vecUnderWord(vec, [-s]);
        if vec = false then
            return false;
        fi;
        sum:= sum + c0 * vec;
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
for k in 6*[0..23] do
    setRow(k+1, 3, basicVec(k+1, u), img);
    setRow(k+1, -3, basicVec(k+1, u1), img);
od;

# spanning tree
for k in 6*[0..23] do
    makeEdge(k+1, k+2, 1);
    makeEdge(k+2, k+3, 3);
    makeEdge(k+3, k+4, 1);
    makeEdge(k+3, k+5, 3);
    makeEdge(k+5, k+6, 1);
od;

# cycles
for k in 6*[0..23] do
    setRow(k+2, 1, 0, gen);
    setRow(k+4, 1, 0, gen);
    setRow(k+6, 1, 0, gen);
    setRow(k+1, -1, 0, inv);
    setRow(k+3, -1, 0, inv);
    setRow(k+5, -1, 0, inv);
od;

# z*
for k in [0..137] do
    makeEdge(k+1, k+7, 4);
od;

for k in 6*[0..22] do
    setRow(k+2, 2, [ -1, -3, 4 ], rel);
    setRow(k+4, 2, [ -1, -3, 4 ], rel);
    setRow(k+6, 2, [ -1, -3, 4 ], rel);
    setRow(k+7, -2, [ -4, 3, 1 ], rel);
    setRow(k+8, -2, [ -4, 3, 1 ], rel);
    setRow(k+9, -2, [ -4, 3, 1 ], rel);
od;

for k in 6*[0..21] do
    setRow(k+13, 2, 0, gen);
    setRow(k+4, -2, 0, inv);
od;

for k in 6*[0..20] do
    setRow(k+4, 3, [ -2, -1, 4 ], rel);
    setRow(k+20, -3, [ -4, 1, 2 ], rel);
    setRow(k+23, 3, 0, gen);
od;

for k in 6*[0..18] do
    setRow(k+16, -3, 0, inv);
od;

for k in 6*[0..19] do
    setRow(k+29, -2, [ -4, 3, 1 ], rel);
od;

for k in 6*[0..18] do
    setRow(k+9, 2, [ -1, 4, -3 ], rel);
    setRow(k+6, -2, 0, inv);
od;

for k in 6*[0..14] do
    setRow(k+35, 2, 0, gen);
od;

for k in 6*[0..17] do
    setRow(k+6, 3, [ -2, -1, 4 ], rel);
od;

for k in 6*[0..14] do
    setRow(k+42, -3, [ -4, 1, 2 ], rel);
od;

setRow(114, 3, 0, gen);
setRow(120, 3, 0, gen);
setRow(126, 3, 0, gen);
setRow(18, -3, 0, inv);
setRow(24, -3, 0, inv);
setRow(30, -3, 0, inv);
setRow(36, -3, 0, inv);

setRow(11, 2, [ -1, 4, -3 ], rel);
setRow(17, 2, [ -1, 4, -3 ], rel);
setRow(23, 2, [ -1, 4, -3 ], rel);
setRow(29, 2, [ -1, 4, -3 ], rel);
setRow(120, -2, [ -4, 3, 1 ], rel);
setRow(126, -2, [ -4, 3, 1 ], rel);
setRow(132, -2, [ -4, 3, 1 ], rel);

setRow(123, 2, 0, gen);
setRow(125, 2, 0, gen);
setRow(129, 2, 0, gen);
setRow(131, 2, 0, gen);
setRow(135, 2, 0, gen);
setRow(137, 2, 0, gen);

setRow(11, -2, 0, inv);
setRow(17, -2, 0, inv);
setRow(23, -2, 0, inv);

setRow(5, -2, [ 4, -2, -4 ], rel);

setRow(5, 3, [ 4, -2, -1 ], rel);
setRow(11, 3, [ 4, -2, -1 ], rel);
setRow(17, 3, [ 4, -2, -1 ], rel);

setRow(130, -3, [ -4, 1, 2 ], rel);
setRow(132, -3, [ -4, 1, 2 ], rel);
setRow(136, -3, [ -4, 1, 2 ], rel);
setRow(138, -3, [ -4, 1, 2 ], rel);
setRow(142, -3, [ -4, 1, 2 ], rel);
setRow(144, -3, [ -4, 1, 2 ], rel);

setRow(2, -3, 0, inv);
setRow(4, -3, 0, inv);
setRow(8, -3, 0, inv);
setRow(10, -3, 0, inv);
setRow(14, -3, 0, inv);

setRow(1, 2, [ -1, -3, 4 ], rel);
setRow(3, 2, [ -1, -3, 4 ], rel);
setRow(7, 2, [ -1, -3, 4 ], rel);

setRow(1, -2, 0, inv);
setRow(2, -2, 0, inv);

setRow(5, 2, 0, gen);

setRow(12, -3, [ -4, 1, 2 ], rel);

setRow(142, 3, 0, gen);
setRow(144, 3, 0, gen);

setRow(3, -2, [ 3, 1, -2, -1, -3 ], rel);

setRow(1, -4, [ -3, -2, -1 ], rel);
setRow(2, -4, [ -3, -2, -1 ], rel);
setRow(3, -4, [ -3, -2, -1 ], rel);
setRow(4, -4, [ -1, -3, -2 ], rel);
setRow(5, -4, [ -3, -2, -1 ], rel);
setRow(6, -4, [ -1, -3, -2 ], rel);

setRow(142, -2, [ 3, -4, 1 ], rel);
setRow(144, -2, [ 3, -4, 1 ], rel);

setRow(136, 3, [ 4, 3, -4 ], rel);
setRow(138, 3, [ 4, 3, -4 ], rel);

setRow(6, -3, [ 1, 2, -4 ], rel);

setRow(130, 3, 0, gen);
setRow(132, 3, 0, gen);

setRow(136, -2, [ -4, 3, 1 ], rel);
setRow(138, -2, [ -4, 3, 1 ], rel);

setRow(140, 2, 0, gen);
setRow(141, 2, 0, gen);
setRow(142, 2, 0, gen);
setRow(143, 2, 0, gen);
setRow(144, 2, 0, gen);

setRow(139, 4, [ 1, 2, 3 ], rel);
setRow(140, 4, [ 1, 2, 3 ], rel);
setRow(141, 4, [ 1, 2, 3 ], rel);
setRow(142, 4, [ 1, 2, 3 ], rel);
setRow(143, 4, [ 1, 2, 3 ], rel);
setRow(144, 4, [ 1, 2, 3 ], rel);

# test
if CHECK_REL then
    Print("testing relations ... \c");
    m12:= mmm[1] * mmm[2];
    m23:= mmm[2] * mmm[3];
    m123:= mmm[1] * m23;
    Print(m123 = mmm[3] * m12, "\n");
    Print(m123 = m23 * mmm[1], "\n");
    Print("testing power ... \c");
    m0:= mmm[1] * mmm[8];
    m2:= mmm[1] * mmm[1];
    Print(a1 * mmm[1] + a0 * m0 = m2, "\n");
    Print("testing power ... \c");
    m2:= mmm[2] * mmm[2];
    m3:= mmm[2] * m2;
    Print(b2 * m2 + b1 * mmm[2] + b0 * m0 = m3, "\n");
    Print("testing power ... \c");
    m2:= mmm[3] * mmm[3];
    m3:= mmm[3] * m2;
    m4:= mmm[3] * m3;
    Print(c3 * m3 + c2 * m2 + c1 * mmm[3] + c0 * m0 = m4, "\n");
fi;
