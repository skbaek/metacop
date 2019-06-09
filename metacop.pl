:- op(1140, xfy, <=>). 
:- op(1130, xfy, =>). 
:- op(500, fy, all). 
:- op(500, fy, ex).
:- op(500, xfy, :).

test0("( -. ph \\/ ph )").  
test1("( ( ( -. ph /\\ -. ps ) \\/ ph ) \\/ ps )"). 
test2("( -. ( ( ph \\/ ps ) \\/ ch ) \\/ ( ( ph \\/ ch ) \\/ ps ) )").

parse_lp(["(" | Rem], Rem). 
parse_rp([")" | Rem], Rem). 
parse_and(["/\\" | Rem], Rem). 
parse_or(["\\/" | Rem], Rem). 
parse_not(["-." | Rem], Rem). 
parse_to(["->" | Rem], Rem). 
parse_iff(["<->" | Rem], Rem). 

parse_neg(["-." | Tks], -Fml, Rem) :- 
  parse_fml(Tks, Fml, Rem). 

parse_disj(Tks, or(Fml1, Fml2), Rem) :- 
  parse_lp(Tks, Tks0), 
  parse_fml(Tks0, Fml1, Tks1), 
  parse_or(Tks1, Tks2),
  parse_fml(Tks2, Fml2, Tks3),
  parse_rp(Tks3, Rem). 

parse_conj(Tks, and(Fml1, Fml2), Rem) :- 
  parse_lp(Tks, Tks0), 
  parse_fml(Tks0, Fml1, Tks1), 
  parse_and(Tks1, Tks2),
  parse_fml(Tks2, Fml2, Tks3),
  parse_rp(Tks3, Rem). 

parse_disj(Tks, or(Fml1, Fml2), Rem) :- 
  parse_lp(Tks, Tks0), 
  parse_fml(Tks0, Fml1, Tks1), 
  parse_or(Tks1, Tks2),
  parse_fml(Tks2, Fml2, Tks3),
  parse_rp(Tks3, Rem). 

parse_atm([Atm | Rem], Atm, Rem) :-
  parse_neg(Tks, Lit, Rem) ; 
  ( Tks = [Atm | Rem], Lit = pos(Atm) ).

parse_fml(Tks, Fml, Rem) :- 
  parse_disj(Tks, Fml, Rem) ;
  parse_conj(Tks, Fml, Rem) ;
  parse_lit(Tks, Fml, Rem).

parse(Str, Fml) :- 
  split_string(Str,  " ", "", Tks),
  parse_fml(Tks, Fml, []).

negate(pos(Atm), neg(Atm)). 
negate(neg(Atm), pos(Atm)). 

complements(neg(Atm), pos(Atm)).
complements(pos(Atm), neg(Atm)).

has_complement(Pth, or(Frm1, Frm2)) :-  
  has_complement(Pth, Frm1) ;
  has_complement(Pth, Frm2).

has_complement(Pth, and(Frm1, Frm2)) :-  
  has_complement(Pth, Frm1) ;
  has_complement(Pth, Frm2).

has_complement(Pth, Lit) :- 
  negate(Lit, NegLit),
  member(NegLit, Pth).

compute_mode(Pth, Frm1, Frm2, Md, Md1, Md2) :- 
  ( Md = start, Md1 = start, Md2 = start ) ;
  ( Md = span, Md1 = span, Md2 = span ) ;
  ( Md = ext,
    ( ( has_complement(Pth, Frm1), Md1 = ext, Md2 = span ) ; 
      ( has_complement(Pth, Frm2), Md1 = ext, Md2 = span ) ) ).

prove(Frm, Prf) :- 
  iterate(Frm, 2, Trc),
  compile(falsum, Frm, falsum, Trc, [], Prf0),
  strings_concat(["? ", Prf0, " copst"], Prf).

iterate(Frm, Lth, Prf) :- 
  search([], Frm, [], Lth, start, Prf) ;
  ( NewLth is Lth + 1, 
    search([], Frm, [], NewLth, start, Prf) ).

fold([Dj], Dj). 
fold([Dj | Djs], or(Dj, Frm)) :- fold(Djs, Frm). 

search(Pth, or(Frm1, Frm2), Dsj, Lth, Md, [Inf | Trc]) :- 
  ( ( search(Pth, Frm1, [Frm2 | Dsj], Lth, Md, Trc), Inf = lft) ;
    ( search(Pth, Frm2, [Frm1 | Dsj], Lth, Md, Trc), Inf = rgt) ).

search(Pth, and(Frm1, Frm2), Dsj, Lth, Md, Trc) :- 
  compute_mode(Pth, Frm1, Frm2, Md, Md1, Md2),
  search(Pth, Frm1, Dsj, Lth, Md1, Trc1), 
  search(Pth, Frm2, Dsj, Lth, Md2, Trc2),
  append(Trc1, Trc2, Trc). 

search([], pos(Atm), Djs, Lth, start, [psh | Trc]) :- 
  Lth \== 0, NewLth is Lth - 1, 
  fold(Djs, Frm),
  search([pos(Atm)], Frm, [], NewLth, ext, Trc).

search(Pth, Lit, _, _, ext, [red]) :- 
  negate(Lit, NegLit), 
  member(NegLit, Pth).

search(Pth, Lit, Djs, Lth, span, Trc) :- 
  ( negate(Lit, NegLit), 
    member(NegLit, Pth), Trc = [red] ) ; 
  ( Lth \== 0, NewLth is Lth - 1, 
    fold(Djs, Frm),
    search([Lit | Pth], Frm, [], NewLth, ext, SubTrc),
    Trc = [psh | SubTrc] ).

strings_concat([], ""). 

strings_concat([Str | Strs], AppStr) :- 
  strings_concat(Strs, SubStr),
  string_concat(Str, SubStr, AppStr). 
   
compile(Pth, and(Frm1, Frm2), Djs, Trc, Rem, Prf) :- 
  compile(Pth, Frm1, Djs, Trc, Trc0, Prf0), 
  compile(Pth, Frm2, Djs, Trc0, Rem, Prf1),
  strings_concat(["? ? ? ? ", Prf0, " ", Prf1, " copsp"], Prf).

compile(Pth, or(Frm1, Frm2), Djs, [Dir | Trc], Rem, Prf) :- 
  ( ( Djs == falsum,  Dir = lft, NewFrm = Frm1, NewDjs = Frm2,          WFPrf = "? ? ? ",   Inf = " coplf" ) ; 
    ( Djs == falsum,  Dir = rgt, NewFrm = Frm2, NewDjs = Frm1,          WFPrf = "? ? ? ",   Inf = " coprf" ) ; 
    ( Djs \== falsum, Dir = lft, NewFrm = Frm1, NewDjs = or(Frm2, Djs), WFPrf = "? ? ? ? ", Inf = " copl" ) ; 
    ( Djs \== falsum, Dir = rgt, NewFrm = Frm2, NewDjs = or(Frm1, Djs), WFPrf = "? ? ? ? ", Inf = " copr" ) ),
  compile(Pth, NewFrm, NewDjs, Trc, Rem, SubPrf),
  strings_concat([WFPrf, SubPrf, Inf], Prf).

compile(Pth, Frm, Djs, [psh | Trc], Rem, Prf) :- 
  compile(or(Pth, Frm), Djs, falsum, Trc, Rem, Prf0),
  strings_concat(["? ? ? ", Prf0, " coppsh"], Prf).

compile(or(_, neg(Atm)), pos(Atm), _, [red | Rem], Rem, "? ? ? copcp"). 
compile(or(_, pos(Atm)), neg(Atm), _, [red | Rem], Rem, "? ? ? copcn"). 

compile(or(Pth, _), Lit, Djs, [red | Trc], Rem, Prf) :- 
  compile(Pth, Lit, Djs, [red | Trc], Rem, Prf0),
  string_concat(Prf0, " ? ? ? coptl", Prf).



