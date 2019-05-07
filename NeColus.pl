% 1. NeColus syntax
% _________________

%--- types ---
type(nat).
type(top).
type(bool).
% A -> B is een (functie)type <= A is een type & B is een type
type(arr(A,B)):-
  type(A),
  type(B).
% A & B is een (intersectie)type <= A is een type & B is een type
type(intersect(A,B)):-
  type(A),
  type(B).
% {l : A} is een (record)type <= A is een type & l is een expressie van type A.
type(rec(L, A)):-
  label(L),
  type(A).

variable(v1).
variable(v2).
variable(v3).

label(l1).
label(l2).


% --- Expressies ---
% \x. E. Hoe juist implementeren ?
expr(lambda(var(X), E)) :-
  variable(X),
  expr(E).

% E1E2 : De applicatie van E1 en E2 <= E1 is een expressie en E2 is een expressie
expr(appl(E1, E2)) :-
  expr(E1),
  expr(E2).


% E1,,E2 : De Merg van E1 en E2 <= E1 is een expressie en E2 is een expressie
expr(merge(E1, E2)) :-
  expr(E1),
  expr(E2).


% E : A : annotated E is van type A <= E is een expressie van type A
expr(annot(E, A)) :-
  expr(E),
  type(A).

% E.l
expr(get_l_from_expr(E,L)):-
    expr(E),
    single_rec(L,E).

expr(var(X)):-
  variable(X).

expr(isZero(E,Y)):-
  expr(E),
  expr(Y).

expr(zero).
expr(one).
expr(expr_top).
expr(true).
expr(false).

% l = E : {l = E} is een singleton record <= l is een record en E is een expressie
expr(single_rec(L, E)) :-
  rec(L,_),
  expr(E).

isZero(zero,true).
isZero(E,false):-
  E \= zero.

% --- Typing context ---

tC([]):-
  !.
tC([annot(var(X),A)|Tail]) :-
  variable(X),
  type(A),
  tC(Tail).

% ------------- Subtyping rules -------------

% fail
sub(_, _,_, 0) :- fail.

% S-Refl: A <: A
sub(A, A,id, N) :-
  N > 0,
  type(A).

% S-Trans: B <: C en A <: B --> A <: C
sub(A, C,after(C1,C2), N) :-
  N > 0,
  N1 is N-1,
  sub(A, B, C2, N1),
  sub(B, C, C1, N1),
  type(A),
  type(B),
  type(C).

% S-Top: A <: T
sub(A, top, to_top, N) :-
  N > 0,
  N1 is N-1,
  type(A).

% S-rcd
sub(rec(L,A),rec(L,B),targ_rec_c(L,C),N):-
  N > 0,
  N1 is N-1,
  sub(A,B,C,N1).

%Beperking op S-arr
sub(arr(_,arr(_,arr(_,T))),T,_,_):- fail.
% S-Arr:
sub(arr(A1, A2), arr(B1, B2), targ_arr_c(C1,C2), N) :-
  N > 0,
  N1 is N-1,
  sub(A2, B2,C2, N1),
  sub(B1, A1,C1, N1),
  type(A1),
  type(A2),
  !,
  type(B1),
  type(B2).

% S-AndL:
sub(intersect(A1, _), A1, proj1, N) :-
  N > 0.

% S-AndR:
sub(intersect(_, A2), A2, proj2, N) :-
  N > 0.

% S-And:
sub(A1, intersect(A2, A3), targ_inters_coerc(C1,C2), N) :-
  N > 0,
  N1 is N-1,
  sub(A1, A2, C1, N1),
  sub(A1, A3, C2, N1).

% S-DistrArr:
sub(intersect(arr(A1, A2), arr(A1, A3)), arr(A1, intersect(A2, A3)),dist_arr, N) :-
  N > 0.

% S-TopArr:
sub(top, arr(top, top), top_to_arr, N) :-
  N > 0.

% S-DistRcd:
sub(intersect(rec(L, A),rec(L, B)), rec(L, intersect(A, B)), dist_l, N) :-
  N > 0.

% S-TopRcd
sub(top, rec(_, top), top_to_rec, N) :-
  N > 0.
% S-ModusPonens
sub(A,C,modusponenscoerc(C1,C2),N):-
  N > 0,
  N1 is N-1,
  sub(A,arr(B,C),C2,N1),
  sub(A,B,C1,N1).

% --- Bidirectional type system ---
% -- Inference --

% De vorm: synthesize(Typing_context, Expression, Type, Target_term)
% -- Typing_context is een NeColus term
% -- Expression is een NeColus expressie
% -- Type is een NeColus(??) type
% -- Target_term is een term uit de doeltaal


% T-top
synthesize(TC,expr_top,top,targ_top):-
  !,
  tC(TC).

% T-lit
synthesize(TC,zero,nat,targ_zero):-
  !,
  tC(TC).
synthesize(TC,one,nat,targ_one):-
  !,
  tC(TC).

% T-bool
synthesize(TC,true,bool,targ_true):-
  !,
  tC(TC).

synthesize(TC,false,bool,targ_false):-
  !,
  tC(TC).
% T-var
synthesize(TC,var(X),A,var(X)):-
  !,
  tC(TC),
  member(annot(var(X),A),TC).

% T-app
synthesize(TC,appl(E1,E2),A2,targ_appl(T_E1,T_E2)):-
  !,
  tC(TC),
  synthesize(TC,E1,arr(A1,A2),T_E1),
  check_type(TC,E2,A1,T_E2).

% T-anno
synthesize(TC,annot(E,A),A,Targ_E):-
  !,
  tC(TC),
  check_type(TC,E,A,Targ_E).

% T-proj
synthesize(TC,get_l_from_expr(E,L),A,get_l_from_targexpr(T_E,L)):-
  !,
  tC(TC),
  synthesize(TC,E,rec(L,A),T_E).

% T-merge
synthesize(TC,merge(E1,E2),intersect(A1,A2),targ_inters_term(T_E1,T_E2)):-
  !,
  tC(TC),
  synthesize(TC,E1,A1,T_E1),
  synthesize(TC,E2,A2,T_E2),
  disj(A1,A2).

% T-rcd
synthesize(TC,single_rec(L,E),rec(L,A),targ_annot(L,T_E)):-
  !,
 tC(TC),
 synthesize(TC,E,A,T_E).

synthesize(TC,isZero(E,Y),arr(nat,bool),targ_isZero(T_E,T_Y)):-
  !,
  tC(TC),
  synthesize(TC,E,nat,T_E),
  synthesize(TC,Y,bool,T_Y).

% -- Checking --

% T-abs
check_type(TC,lambda(var(X),E),arr(A,B),targ_lambda(var(X),T_E)):-
  !,
  tC(TC),
  (
  check_type([annot(var(X),A)|TC],E,B,coerce(C,CE)) ->
    step(coerce(C,CE),T_E)
  ;
  check_type([annot(var(X),A)|TC],E,B,T_E)
  ).

% T-sub
check_type(TC,E,A,coerce(C,T_E)):-
  tC(TC),
  synthesize(TC,E,B,T_E),
  sub(B,A,C,4). %aantal iteraties is hier geïnstantieerd, oke?

check_type(TC,isZero(zero,Y),bool,targ_isZero(targ_zero,T_Y)):-
  tC(TC),
  synthesize(TC,Y,bool,T_Y).

check_type(TC,isZero(one,Y),bool,targ_isZero(targ_one,T_Y)):-
  tC(TC),
  synthesize(TC,Y,bool,T_Y).
% _______________________________________________________________
% T-ModusPonens
% Dit zijn specifieke regels die zeggen dat je het functietype uit een merge-type haalt. Het kan ook annders,
% maar voorlopig houden we het zo specifiek als dit omdat het zo gemakkelijker is om beperkingen specifiek
% voor problemen die we hier zijn tegengekomen op te leggen en zo die problemen op te lossen.

%check_type(TC,E,Z,targ_appl(F,coerce(C,T_E))):-
%  check_type(TC,E,X,F),
%  check_type(TC,E,arr(Y,Z),T_E),
%  disj(X,Z), %Onze disjunctieregels houden geen rekening met Modus Ponens...
%  sub(X,Y,C,2). %aantal iteraties is hier geïnstantieerd, oke?

% ______________________________________________________________
% --------- Disjointness rules ----------------------


disj(A,A):- fail.

% D-TopL
disj(top,A):-
  type(A).

% D-TopR
disj(A,top):-
    type(A).

%D-Bool
disj(bool,nat).

%D-BoolR
disj(nat,bool).

% D-Arr
disj(arr(_,A2),arr(_,B2)):-
  disj(A2,B2).

% D-AndL
disj(intersect(A1,A2),B):-
  disj(A1,B),
  disj(A2,B).

% D-AndR
disj(A,intersect(B1,B2)):-
  disj(A,B1),
  disj(A,B2).

% D-RecEq
disj(rec(lRec,A),rec(lRec,B)):-
  disj(A,B).

% D-RecNeq
disj(rec(L1,_),rec(L2,_)):-
  L1 \== L2.

% D-AxNatArr
%vervangen door de disjunctieregel D-ModusPonens

% D-AxArrNat
%vervangen door de disjunctieregel D-ModusPonens

% D-AxNatRcd
disj(nat,rec(_,_)).

% D-AxRcdNat
disj(rec(_,_),nat).

% D-AxArrRcd
disj(arr(_,_),rec(lRec,_)).

% D-AxRcdArr
disj(rec(lRec,_),arr(_,_)).

% ______________________________________________________________
% D-ModusPonens
disj(A,arr(B,C)):-
  disj(A,C).
disj(arr(B,C),A):-
  disj(A,C).
% ______________________________________________________________
% 2. Target taal syntax
% _____________________ p. 22:12

% --- target types --- (figure 7)

% Nat
targ_type(targ_nat).
% <>
targ_type(targ_top_type).

%targ_bool
targ_type(targ_bool).
% t1 x t2
targ_type(targ_interstype(T1,T2)):-
    targ_type(T1),
    targ_type(T2).
% t1 -> t2
targ_type(targ_arr_t(T1,T2)):-
    targ_type(T1),
    targ_type(T2).
% {l:t}
targ_type(targ_rec_t(L,T)):-
  label(L),
  targ_type(T).


% --- target typing contexts ---
targ_typing_context([]).
targ_typing_context([targ_annot(var(X),A)|Tail]):-
    variable(X),
    targ_type(A),
    targ_typing_context(Tail).


% --- target terms ---

% x
targ_term(var(X)):-
  variable(X).

% i
targ_term(targ_zero).
targ_term(targ_one).

% <>
targ_term(targ_top).
%targ_true & targ_false
targ_term(targ_true).
targ_term(targ_false).

% \x.e
targ_term(targ_lambda(var(X),E)):-
  variable(X),
  targ_term(E).

% e1 e2
targ_term(targ_appl(E1,E2)):-
    targ_term(E1),
    targ_term(E2).

% <e1, e2>
targ_term(targ_inters_term(E1,E2)):-
    targ_term(E1),
    targ_term(E2).

% e.l
targ_term(get_l_from_targexpr(E,L)):-
    targ_term(E),
    singleton_targ_rec(L,_).

% {l=e}
targ_term(singleton_targ_rec(L,E)):-
    targ_rec_t(L,_),
    targ_term(E).

% c e
targ_term(coerce(C,E)):-
  targ_term(E),
  coercion(C).

targ_term(targ_isZero(E,Y)):-
  targ_term(E),
  targ_term(Y).

targ_isZero(targ_zero,targ_true).
targ_isZero(X,targ_false):-
  X \= targ_zero.
% --- coercions ---

% id
coercion(id).

% c1 ° c2
coercion(after(C1,C2)):-
    coercion(C1),
    coercion(C2).

% top
coercion(to_top).

% top_{->}
coercion(top_to_arr).

% top_{l}
coercion(top_to_rec).

% c1 -> c2
coercion(targ_arr_c(C1,C2)):-
    coercion(C1),
    coercion(C2).

% <c1,c2>
coercion(targ_inters_coerc(C1,C2)):-
    coercion(C1),
    coercion(C2).

% proj1
coercion(proj1).

% proj2
coercion(proj2).

% {l : c}
coercion(targ_rec_c(_,C)):-
    coercion(C).

% dist_{l}
coercion(dist_l).

% dist_{->}
coercion(dist_arr).

% Modus Ponens
coercion(modusponenscoerc(C1,C2)):-
  coercion(C1),
  coercion(C2).

% --- Target values ---

% \x.e
targ_value(targ_lambda(var(_),_)).

% <>
targ_value(targ_top).

% i
targ_value(targ_one).
targ_value(targ_zero).

% true & false
targ_value(targ_true).
targ_value(targ_false).

% <v1, v2>
targ_value(targ_inters_term(V1, V2)) :- %tuple
  targ_value(V1),
  targ_value(V2).

% (c1 -> c2) v
targ_value(coerce(targ_arr_c(C1, C2), V)) :-
  targ_value(V).

% dist_{->} v
targ_value(coerce(dist_arr, V)) :-
  targ_value(V).

% top_{->} v
targ_value(coerce(top_to_arr, V)) :-
  targ_value(V).

% --- Target typing ---

% De vorm: targ_synth(Targ_typing_context, Target_term, Targ_type)
% -- Targ_typing_context is een typing context uit de doeltaal
% -- Target_term is een doeltaal expressie (=term)
% -- Type is een type uit de doeltaal

% TYP-unit
targ_synth(TTC, targ_top, targ_top_type):-
  targ_typing_context(TTC).

% TYP-lit
targ_synth(TTC,targ_zero,targ_nat):-
  targ_typing_context(TTC).
targ_synth(TTC,targ_one, targ_nat):-
  targ_typing_context(TTC).
% TYP-bool
targ_synth(TTC,targ_true,targ_bool):-
  targ_typing_context(TTC).
targ_synth(TTC,targ_false,targ_bool):-
  targ_typing_context(TTC).
% TYP-var
targ_synth(TTC,var(X),T):-
  targ_typing_context(TTC),
  member(annot(var(X),T),TTC).

% TYP-abs
targ_synth(TTC, targ_lambda(var(X),E),targ_arr_t(T1,T2)):-
  targ_term(targ_lambda(var(X),E)),
  targ_typing_context(TTC),
  targ_synth(TTC1,E,T2),
  append([targ_annot(var(X),T1)],TTC,TTC1).

% TYP-app
targ_synth(TTC,targ_appl(E1,E2),T2):-
  targ_typing_context(TTC),
  targ_synth(TTC,E1,targ_arr_t(T1,T2)),
  targ_synth(TTC,E2,T1).

% TYP-Pair
targ_synth(TTC,targ_inters_term(E1,E2),targ_interstype(T1,T2)):-
  targ_typing_context(TTC),
  targ_synth(TTC,E1,T1),
  targ_synth(TTC,E2,T2).

% TYP-capp
targ_synth(TTC,coerce(C,E),T2):-
  targ_typing_context(TTC),
  targ_synth(TTC,E,T1),
  cotyp(C,T1,T2),
  !.

% TYP-rcd
targ_synth(TTC,singleton_targ_rec(L,E),targ_rec_t(L,T)):-
  targ_typing_context(TTC),
  targ_synth(TTC, E,T).

% TYP-proj
targ_synth(TTC,get_l_from_targexpr(E,L),T):-
  targ_typing_context(TTC),
  targ_synth(TTC,E,targ_rec_t(L,T)).

targ_synth(TTC,targ_isZero(E,Y),targ_bool):-
  targ_typing_context(TTC).

% --- Coercion typing ---

% De vorm: cotyp(Coecion, Targ_type1, Targ_type2)
% -- Coercion is een afleiding van target type 1 naar target type 2
% -- Targ_type1 is een type in de doeltaal
% -- Targ_type2 is een type in de doeltaal, afgeleid door de coercion

% CoTyp-Refl
cotyp(id,T,T).

% CoTyp-Trans
cotyp(after(C1,C2),T1,T3):-
  cotyp(C2,T1,T2),
  cotyp(C1,T2,T3).

% CoTyp-Top
cotyp(to_top, _ ,targ_top_type).

% CoTyp-TopArr
cotyp(top_to_arr,targ_top_type, targ_arr_t(targ_top_type,targ_top_type)).

% CoTyp-TopRcd
cotyp(top_to_rec,targ_top_type,targ_rec_t(_,targ_top_type)).

% CoTyp-Arr
cotyp(targ_arr_c(C1, C2), targ_arr_t(T1, T2), targ_arr_t(T1m,T2m)) :-
  cotyp(C1, T1m, T1),
  cotyp(C2, T2, T2m).

% CoTyp-Pair
cotyp(targ_inters_coerc(C1, C2), T1, targ_interstype(T2, T3)) :-
  cotyp(C1, T1, T2),
  cotyp(C2, T1, T3).

% CoTyp-ProjL
cotyp(proj1, targ_interstype(T1, T2), T1).

% CoTyp-ProjR
cotyp(proj2, targ_interstype(T1, T2), T2).

% CoTyp-Rcd
cotyp(targ_rec_c(L, C), targ_rec_t(L, T1), targ_rec_t(L, T2)) :-
  cotyp(C, T1, T2).

% CoTyp-DistRcd
cotyp(dist_l, targ_interstype(targ_rec_t(L, T1), targ_rec_t(L, T2)), targ_rec_t(L, targ_interstype(T1, T2))).

% CoTyp-DistrArr
cotyp(dist_arr, targ_interstype(targ_arr_t(T1, T2), targ_arr_t(T1, T3), targ_arr_t(T1, targ_interstype(T2, T3)))).

% CoTyp-ModusPonens
cotyp(modusponenscoerc(C1,C2),T,T2):-
  cotyp(C1,T,T1),
  cotyp(C2,T,targ_arr_t(T1,T2)).

% --- Coercion reduction = Step ---

step(targ_top, targ_top).
step(targ_one, targ_one).
step(targ_zero, targ_zero).
step(targ_true, targ_true).
step(targ_false, targ_false).
step(targ_lambda(X,Y),targ_lambda(X,Y1)):-
  step(Y,Y1).
step(targ_isZero(E,Y),targ_isZero(Et,Yt)):-
  step(E,Et),
  step(Y,Yt).

step(targ_inters_term(T1,T2),targ_inters_term(V1,V2)):-
  step(T1,V1),
  step(T2,V2).

% STEP-id
step(coerce(id,W),V):-
  !,
  W \= coerce(_,_),
  step(W,V).

% STEP-Trans
step(coerce(after(C1, C2), V), R) :-
  !,
  step(coerce(C2, V), R2),
  step(coerce(C1, R2), R).

% STEP-Top
step(coerce(to_top,V),targ_top).

% STEP-TopArr
step(targ_appl(coerce(top_to_arr, targ_top), targ_top), targ_top).

% STEP-TopRcd
step(coerce(top_to_rec, targ_top), singleton_targ_rec(_,targ_top)).

% STEP-Pair
step(coerce(targ_inters_coerc(C1,C2),V),targ_inters_term(R1,R2)):-
  !,
  step(coerce(C1,V),R1),
  step(coerce(C2,V),R2).

% STEP-Arr
step(targ_appl(coerce(targ_arr_c(C1,C2),V1),V2),R):-
  !,
  step(coerce(C1,V2),R1),
  step(coerce(C2,targ_appl(V1,R1)),R).

% STEP-DistrArr
step(targ_appl(coerce(dist_arr,targ_inters_term(V1,V2)),V3),targ_inters_term(targ_appl(V1,V3,targ_appl(V2,V3)))).

% STEP-ProjL
step(coerce(proj1,targ_inters_term(V1,V2)),V1).

% STEP-ProjR
step(coerce(proj2,targ_inters_term(V1,V2)),V2).

% STEP-CRcd
step(coerce(targ_rec_t(L,C),singleton_targ_rec(L,V)),singleton_targ_rec(L,R)):-
  !,
  step(coerce(C,V),R).

% STEP-DistRcd
step(coerce(dist_l,targ_inters_term(singleton_targ_rec(L,V1),singleton_targ_rec(L,V2))),singleton_targ_rec(L,targ_inters_term(V1,V2))).

% STEP-Beta
step(targ_appl(targ_lambda(var(X),E), V), Res) :-
  %In expressie E, vervang X door V
  replace(E, X, V, ResExpr),
  step(ResExpr,Res).

replace(targ_isZero(_,Y),X,V,Y_T):-
  targ_isZero(V,Y_T).

replace(E,X,V,E):-
  E \= targ_isZero(_,_).



% STEP-projRcd
step(get_l_from_targexpr(singleton_targ_rec(L,V), L), V).

% STEP-App1
step(targ_appl(E1, E2), targ_appl(E1m, E2)) :-
  step(E1, E2),
  E1m \= E1.

% STEP-App2
step(targ_appl(V1, E2), targ_appl(V1, E2m)) :-
  step(E2, E2m),
    E2 \= E2m.

% STEP-Pair1
step(targ_inters_term(E1, E2), targ_inters_term(E1m, E2)) :-
  step(E1, E1m),
  E1 \= E1m.

% STEP-Pair2
step(targ_inters_term(V1, E2), targ_inters_term(V1, E2m)) :-
  step(E2, E2m),
  E2 \= E2m.

% STEP-Rcd1
step(singleton_targ_rec(L, E), singleton_targ_rec(L, Em)) :-
  step(E, Em),
  E \= Em.

% STEP-Rcd2
step(get_l_from_targexpr(E, L), get_l_from_targexpr(Em, L)) :-
  step(E, Em),
  E \= Em.

% STEP-ModusPonens
step(coerce(modusponenscoerc(C1,C2),V),W):-
  step(coerce(C1,V),E),
  step(coerce(C2,V),F),
  step(targ_appl(F,E),W). %is dit correct?

% STEP-Capp
step(coerce(C, E), coerce(C, Em)) :-
  step(E, Em),
  E \= Em.


% Wat willen we doen?
% -------------------
% find_targ_value_from_NeColus_Expression(NeColus_Expression, NeColus_Type)
% NeColus_Expression is een NeColus Expressie
% NeColus_type is het type waarmee je de expressie wilt typeren om een bepaalde operatie te kunnen doen
% bv. in ((True,,1),,f) + 5 moet ((True,,1),,f) getypeerd worden als nat
% Targ_value is de value uit de doeltaal die geresoleerd wordt uit de gevonden coercions.
% Als eenzelfde combinatie NeColus_Type + NeColus_Expression twee keer een andere Targ_value oplevert, hebben we incoherentie
% gevonden.

%Maak hier nog eentje voor een check_type met lamba als resultaat.
find_targ_value_from_NeColus_Expression(NE,NT,Targ_value,Complete_NT):- %We geven het volledige NeColus type gewoon mee, dat is gemakkelijker
  check_type(TC,NE,NT,coerce(modusponenscoerc(C1,C2),Targ_Term)),
  coercion(modusponenscoerc(C1,C2)),
  translate_typing_context(TC,TTC),
  translate_type(NT,Targ_Type),
  targ_synth(TTC,coerce(C1,Targ_Term),B),
  targ_synth(TTC,coerce(C2,Targ_Term),targ_arr_t(B,Targ_Type)), %haal de functie eruit
  translate_type(Complete_NT,Complete_Targ_Type),
  cotyp(modusponenscoerc(C1,C2),Complete_Targ_Type,Targ_Type),
  step(coerce(modusponenscoerc(C1,C2),Targ_Term),Targ_value).


find_targ_value_from_NeColus_Expression(NE,NT,Targ_value,Complete_NT,C):- %We geven het volledige NeColus type gewoon mee, dat is gemakkelijker
  check_type(TC,NE,NT,coerce(C,Targ_Term)),
  coercion(C),
  translate_typing_context(TC,TTC),
  translate_type(NT,Targ_Type),
  targ_synth(TTC,coerce(C,Targ_Term),Targ_Type),
  translate_type(Complete_NT,Complete_Targ_Type),
  cotyp(C,Complete_Targ_Type,Targ_Type),
  step(coerce(C,Targ_Term),Targ_value).


translate_typing_context([],[]).
translate_typing_context([annot(var(X),A)|TC],[targ_annot(var(X),B)|TTC]):-
  translate_type(A,B),
  translate_typing_context(TC,TTC).

translate_type(nat,targ_nat).
translate_type(top,targ_top_type).
translate_type(bool,targ_bool).
translate_type(arr(A,B),targ_arr_t(At,Bt)):-
  translate_type(A,At),
  translate_type(B,Bt).
translate_type(intersect(A,B),targ_interstype(At,Bt)):-
  translate_type(A,At),
  translate_type(B,Bt).
translate_type(rec(L,A),targ_rec_t(L,At)):-
  translate_type(A,At).
