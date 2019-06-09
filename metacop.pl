#!/usr/bin/env swipl

:- initialization(main, main).

% :- op(1140, xfy, <=>). 
% :- op(1130, xfy, =>). 
% :- op(500, fy, all). 
% :- op(500, fy, ex).
% :- op(500, xfy, :).

test0("( -. ph \\/ ph )").  
test1("( ( ( -. ph /\\ -. ps ) \\/ ph ) \\/ ps )"). 
test2("( -. ( ( ph \\/ ps ) \\/ ch ) \\/ ( ( ph \\/ ch ) \\/ ps ) )").

parse_lp(["(" | Rem], Rem). 
parse_rp([")" | Rem], Rem). 

parse_conn(["\\/" | Tks], Fml1, Fml2, or(Fml1, Fml2),  Tks). 
parse_conn(["/\\" | Tks], Fml1, Fml2, and(Fml1, Fml2), Tks). 
parse_conn(["->" | Tks],  Fml1, Fml2, to(Fml1, Fml2),  Tks). 
parse_conn(["<->" | Tks], Fml1, Fml2, iff(Fml1, Fml2), Tks). 

parse_neg(["-." | Tks], -Fml, Rem) :- 
  parse_fml(Tks, Fml, Rem). 

parse_bin(Tks, Fml, Rem) :- 
  parse_lp(Tks, Tks0), 
  parse_fml(Tks0, Fml1, Tks1), 
  parse_conn(Tks1, Fml1, Fml2, Fml, Tks2),
  parse_fml(Tks2, Fml2, Tks3),
  parse_rp(Tks3, Rem). 

parse_atm([Atm | Rem], Atm, Rem) :-
  member(Atm, ["ph", "ps", "ch", "th", "ta", "et", "ze", "si", "rh", "mu", "la", "ka"]).

parse_fml(Tks, Fml, Rem) :- 
  parse_bin(Tks, Fml, Rem) ;
  parse_neg(Tks, Fml, Rem) ;
  parse_atm(Tks, Fml, Rem).

parse(Str, Fml) :- 
  split_string(Str, " ", "", Tks),
  parse_fml(Tks, Fml, []).

conjugate(Lit, CnjLit) :- 
  Lit = -Atm -> 
  CnjLit = Atm ;
  CnjLit = -Lit.

% complements(neg(Atm), pos(Atm)).
% complements(pos(Atm), neg(Atm)).

% normalize(or(Frm1, Frm2), or(Nrm1, Nrm2)) :-  
%   normalize(Frm1, Nrm1), normalize(Frm2, Nrm2). 
% normalize(and(Frm1, Frm2), and(Nrm1, Nrm2)) :-  
%   normalize(Frm1, Nrm1), normalize(Frm2, Nrm2). 
% normalize(to(Frm1, Frm2), or(Nrm1, Nrm2)) :-  
%   normalize(-Frm1, Nrm1), normalize(Frm2, Nrm2). 
% normalize(iff(Frm1, Frm2), and(Nrm1, Nrm2)) :-  
%   normalize(to(Frm1, Frm2), Nrm1), 
%   normalize(to(Frm2, Frm1), Nrm2). 
% normalize(-or(Frm1, Frm2), and(Nrm1, Nrm2)) :-  
%   normalize(-Frm1, Nrm1), normalize(-Frm2, Nrm2). 
% normalize(-and(Frm1, Frm2), or(Nrm1, Nrm2)) :-  
%   normalize(-Frm1, Nrm1), normalize(-Frm2, Nrm2). 
% normalize(-to(Frm1, Frm2), and(Nrm1, Nrm2)) :-  
%   normalize(Frm1, Nrm1), normalize(-Frm2, Nrm2). 
% normalize(-iff(Frm1, Frm2), Nrm) :-  
%   normalize(iff(Frm1, -Frm2), Nrm). 
% normalize(--Frm, Nrm) :- normalize(Frm, Nrm).
% normalize(-Frm, -Frm).

conjuncts(and(Frm1, Frm2), Frm1, Frm2). 
conjuncts(-or(Frm1, Frm2), -Frm1, -Frm2). 
conjuncts(-to(Frm1, Frm2), Frm1, -Frm2). 
conjuncts(iff(Frm1, Frm2), to(Frm1, Frm2), to(Frm2, Frm1)). 

disjuncts(or(Frm1, Frm2), Frm1, Frm2). 
disjuncts(to(Frm1, Frm2), -Frm1, Frm2). 
disjuncts(-and(Frm1, Frm2), -Frm1, -Frm2). 
disjuncts(-iff(Frm1, Frm2), and(Frm1, -Frm2), and(Frm2, -Frm1)). 

juncts(Frm, Frm1, Frm2) :- 
  conjuncts(Frm, Frm1, Frm2) ;
  disjuncts(Frm, Frm1, Frm2).

complementary(Pth, Frm) :-  
  juncts(Frm, Frm1, Frm2) ->
  ( complementary(Pth, Frm1) ; complementary(Pth, Frm2) ) ;
  ( conjugate(Frm, CnjFrm), member(CnjFrm, Pth) ).

compute_mode(Pth, Frm1, Frm2, Md, Md1, Md2) :- 
  ( Md = start, Md1 = start, Md2 = start ) ;
  ( Md = span, Md1 = span, Md2 = span ) ;
  ( Md = ext,
    ( ( complementary(Pth, Frm1), Md1 = ext, Md2 = span ) ; 
      ( complementary(Pth, Frm2), Md1 = ext, Md2 = span ) ) ).

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

search(Pth, Frm, Dsj, Lth, Md, Trc) :- 
  disjuncts(Frm, Frm1, Frm2),
  ( ( search(Pth, Frm1, [Frm2 | Dsj], Lth, Md, Trc0), Trc = lft(Trc0) ) ;
    ( search(Pth, Frm2, [Frm1 | Dsj], Lth, Md, Trc0), Trc = rgt(Trc0) ) ).

search(Pth, Frm, Dsj, Lth, Md, split(Trc0, Trc1)) :- 
  conjuncts(Frm, Frm1, Frm2)
  compute_mode(Pth, Frm1, Frm2, Md, Md1, Md2),
  search(Pth, Frm1, Dsj, Lth, Md1, Trc0), 
  search(Pth, Frm2, Dsj, Lth, Md2, Trc1).

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

main([Argv | _]) :-
  atom_string(Argv, Str),
  parse(Str, Fml),
  print(Fml).