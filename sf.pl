%% -*- mode: prolog; coding: utf-8 -*-

%% La majorité du code était fourni par l'enseignant. Rechercher "DÉBUT CODE"
%% pour retrouver le code que j'ai écris. (Francis Lalonde)
%% (excepté la coquille détectée à la ligne 44, voir commentaire)

%% eval_decls(+Env, +Decls, -Res)
%% Évalue une liste de déclarations et renvoie dans Res l'expression finale.
eval_decls(Env, [Last], Res) :-
    !, print_message(debug('SF'), elaboratingMain(Last)),
    %% spy(eval),
    elaborate(Env, Last, Expanded),
    %% nospy(eval),
    print_message(debug('SF'), elaborated(Expanded)), % trace,
    check(Env, Expanded, T),
    print_message(debug('SF'), type_is(T)),
    eval(Env, Expanded, Res).
eval_decls(Env, [Decl | Decls], Res) :-
    print_message(debug('SF'), elaborating(Decl)),
    elaborate(Env, Decl, Expanded),
    print_message(debug('SF'), elaborated(Expanded)),
    eval_decl(Env, Expanded, NewEnv),
    print_message(debug('SF'), processed(Decl)),
    eval_decls(NewEnv, Decls, Res).

eval_decl(Env, X : T, NewEnv) :-
    atom(X),
    %% spy(check),
    % elaborate(Env, T, TE),
    print_message(debug('SF'), declare(X,T)),
    check(Env, T, type),

    NewEnv = [(X,T,forward) | Env].
eval_decl(Env, define(X, E), NewEnv) :-
    atom(X),
    print_message(debug('SF'), defining(X)),
    (lookup(Env, X, T, forward) ->
         %spy(check),
         check(Env, E, T);
     print_message(debug('SF'), checking(X)),
     check(Env, E, T)),
    print_message(debug('SF'), define(X, T)),
    NewEnv = [(X,T,V) | Env],
    eval(NewEnv, E, V). 
    %% Découverte d'une coquille ici. Ligne de code originale :
    %% eval(Env, E, V).



%% lookup(+Env, +Var, -Type, -Val)
%% Renvoie le type (et la valeur) de Var dans Env.
lookup(Env, X, T, V) :- member((X, T1, V1), Env), !, T1 = T, V1 = V.


%% remove(+X, +List, -Res)
%% Renvoie une liste Res identique à List, sauf avec X en moins.
remove(_, [], []).
remove(X, [X|YS], ZS) :- !, remove(X, YS, ZS).
remove(X, [Y|YS], [Y|ZS]) :- remove(X, YS, ZS).

%% union(+Set1, +Set2, -Set)
%% Renvoie l'union de deux sets.  Si ni Set1 ni Set2 n'ont de duplicats, alors
%% le résultat n'en aura pas non plus.
union([], YS, YS).
union(XS, [], XS).
union([X|XS], YS, ZS) :-
    union(XS, YS, S),
    (member(X, YS) -> ZS = S; ZS = [X|S]).

%% freevars(+Exp, -Freevars)
%% Renvoie les variables libres de Exp.
freevars(N, []) :- number(N).
freevars(DontCare, []) :- var(DontCare), !.
freevars(quote(_), []).
freevars(X, [X]) :- atom(X).
freevars(forall(X, T), FVs) :-
    freevars(T, FV), remove(X, FV, FVs).
freevars(fn(X, E), FVs) :-
    freevars(E, FV), remove(X, FV, FVs).
freevars(tfn(X, E), FVs) :-
    freevars(E, FV), remove(X, FV, FVs).
%% Pour n'importe quel autre terme composé (genre "app(E1, E2)"), applique
%% freevars récursivement sur ses arguments.
freevars([[]], []) :- !.
freevars(E, FV) :-
    E =.. [_|[Arg|Args]],
    freevars(Arg, FVa),
    freevars(Args, FVas),
    union(FVa, FVas, FV).


%% subst(+Exp, +Var, +Val, -NewExp)
%% Renvoie la substitution de Var par Val dans Exp.
subst(Exp, X, V, NewExp) :- freevars(V, FV), subsT(Exp, X, V, FV, NewExp).
%% subsT(+Exp, +Var, +Val, +FVval, -NewExp)
%% Prédicat auxiliaire interne à "subst".
subsT(X, _, _, _, X) :- var(X), !.
subsT(X, X, V, _, V) :- !.
subsT(X, Y, _, _, X) :- atomic(X), !, X \= Y.
subsT(quote(V), _, _, _, quote(V)).
subsT(Fn, Y, V, FV, Exp) :-
    (Fn = fn(_, _); Fn = tfn(_, _); Fn = forall(_,_)),
    !,
    Fn =.. [Head,X,E],
    (member(X, FV), freevars(E, FVe), member(Y, FVe) ->
         %% V fait référence à un autre X et Y apparaît dans E: appliquer le
         %% renommage α et ressayer pour éviter la capture de nom.
         new_atom(X, NewX),
         subsT(E, X, NewX, [NewX], NewE),
         subsT(NewE, Y, V, FV, NewerE),
         Exp =.. [Head,NewX,NewerE];
     X = Y ->
         %% Y est caché par X.
         Exp = Fn;
     subsT(E, Y, V, FV, Es),
     Exp =.. [Head,X, Es]).
%% Pour n'importe quel autre terme composé (genre "app(E1, E2)"), applique
%% subsT récursivement sur ses arguments.
subsT([[]], _, _, _, [[]]) :- !.
subsT(E, Y, V, FV, Exp) :-
    E =.. [Head|[Arg|Args]],
    subsT(Arg, Y, V, FV, NewArg),
    subsT(Args, Y, V, FV, NewArgs),
    Exp =.. [Head|[NewArg|NewArgs]].

check_type(T1, T2) :-
    T1 = T2 -> true;
    print_message(error, type_mismatch(T1, T2)), fail.

%% check(+Env, +Exp, ?Type)
%% Vérifie/infère le type d'une expression.  Utilisé aussi pour vérifier
%% si une expression de type est valide.

check_type(T1, T2) :-
    T1 = T2 -> true;
    print_message(error, type_mismatch(T1, T2)), fail.


%% %% %% DÉBUT CODE (Francis Lalonde)

%% check(+Env, +Exp, ?Type)
%% Vérifie/infère le type d'une expression.  Utilisé aussi pour vérifier
%% si une expression de type est valide.
check(Env, X, T1) :- atom(X), lookup(Env, X, T2, _), !, check_type(T1, T2).
check(_, N, int) :- number(N).
check(_, quote(_), sexp).   %%verifier

%%ajouter un check de macro pour macroexpander?
check(Env, list(T1), type) :- check(Env,T1,type).

check(Env,T1 -> T2, type) :- 
    check(Env,T1,type), 
    check(Env,T2,type).

check(Env, if(ET,E1,E2), T1) :- 
    check(Env,ET,bool),
    check(Env,E1,T1),
    check(Env,E2,T1).

check(Env,fn(X,E1),(T1->T2)) :- 
    check([(X,T1,_)|Env],E1,T2),!.

check(Env,app(E1,E2),T2) :-
    check(Env,E1,T1->T2), 
    check(Env,E2,T1), !.

check(Env,forall(A1,T1),type) :- 
    check([(A1,type,_)|Env],T1,type), !. 

check(Env,tfn(A,E),forall(A,T)) :-
    check([(A, type, A)|Env],E,T), T =.. TS, member(A,TS), ! ;
    check([(A, type, _)|Env],E,T).   


check(Env,tapp(E1,T1),T3) :-
    check(Env,E1,forall(A1,T2)),
    subst(T2,A1,T1,T3), !;

    % par mesure de sécurité
    check(Env,E1,forall(A1,T2)),
    check(Env,T1,type),
    subst(T2,A1,T1,T3).


%% lemon s'occupe de désucrer fun(e1,e2,...,e_n). Odeur de fraîcheur en bonus. 
%% lemon(+Env, +Exp_in, ACC, -Exp_out) 
lemon(Env, [X|XS], PRE, E2) :- 
    length(XS, N), N=0 ->
        %% Si XS est vide, on retourne avec la nouvelle liste de app
        elaborate(Env, X, X_Out),
        E2 = app(PRE, X_Out);
        %% Sinon, on recommence l'opération avec le reste de la liste(XS), 
        %% avec la nouvelle liste de app
        elaborate(Env, X, X_Out),
        lemon(Env, XS, app(PRE, X_Out), E2).

%% lemon(+Env, +Exp_in, -Exp_out) 
lemon(Env, E, E2) :-
    E =.. [Name | [Arg]],
    length([Arg], N), N=1 ->
           
        % si N = 1
        elaborate(Env, Arg, Exp_Out),
        E2 = app(Name, Exp_Out);
        
        % sinon
        E =.. [Name | Arg], 
        Arg = [Head|ArgS],
        elaborate(Env, Head, E1),
        lemon(Env, ArgS, app(Name, E1), E2).


%% cherche l'environnement pour déterminer si une fonction est polymorphe ou non
%% redirige vers le désucrage avec tapp si polymorphe, normalement sinon.
% searchEnv(+Env, +Name, +Actuals, +Exp, -Exp)
searchEnv(Env, Name, Actuals, E1, E2) :- 
    member((Name, X, V), Env),
    (X = forall(_, MoreTapp) ->                     % si type forall
        tappIt(MoreTapp, tapp(Name, _), Tapp_Out), 
        E1 =.. [_ | ES], 
        lemon(Env, ES, Tapp_Out, E2) ;
                                             
        V = macro(closure(Z, _, Y)) ->              % Sinon, gestion de macro     
            eval([(Z,list(sexp),Actuals)|Env], Y, Expanded),
            elaborate(Env, Expanded, E2)),          
    !;                                              % XOR
    lemon(Env, E1, E2).                             % autres appels

% cherche le type en profondeur
tappIt(Check_in, E, Check_out) :-
    (Check_in = forall(_, MoreTapp)),               % autre forall?
    tappIt(MoreTapp, tapp(E, _), Check_out), !;     % si oui
    Check_out = E.                                  % si non

%% elaborate(+Env, +Exp, -NewExp)
%% Renvoie la version expansée de Exp, ce qui inclus:
%% - expansion de macros.
%% - expansion du sucre syntaxique fun(arg1, arg2, ...).
%% - ajout des instantiations de types.


% pour les fonction polymorphiques sans arguments (e.g. nil)
elaborate(Env, Name, tapp(Name, _)) :- 
    member((Name, forall(_, _), _), Env), !.

% passthrough pour expression déjà bien formée
elaborate(_, tapp(Name, T1), tapp(Name,T1)) :- !.

% cas de base, en passthrough.
elaborate(_, N, N) :- number(N), !.    % cut pour éviter de retourner à _ .
elaborate(_, X, X) :- atom(X), !.      % idem
elaborate(_, quote(E), quote(E)) :- !. % re-idem

% déclaration de type
elaborate(_, X:T, X:T) :- !.         

% define
elaborate(Env, define(X,E), define(X, NewExp)) :- elaborate(Env, E, NewExp), !.

% if
elaborate(Env, if(E1,E2,E3), if(E4, E5, E6)) :- elaborate(Env, E1, E4),
                                                elaborate(Env, E2, E5),
                                                elaborate(Env, E3, E6).

% macro
elaborate(Env, macro(E1), app(macro, E2)) :- elaborate(Env, E1, E2).

% app
elaborate(Env, app(E1, E2), app(E3, E4)) :- 
    elaborate(Env, E1, E3),
    elaborate(Env, E2, E4).

% fn
elaborate(Env, fn(ARGS_in, E_in), fn(ARGS_out, E_out)) :- 
    elaborate(Env, ARGS_in, ARGS_out),
    elaborate(Env, E_in, E_out).

% tfn
elaborate(Env, tfn(TYPE, E_in), tfn(TYPE, E_out)) :-
    elaborate(Env, E_in, E_out).


%% catch-all pour appels, e.g. une fonction E1(args).
elaborate(Env, E1, E2) :- 
    E1 =.. [Name | Actuals],
    searchEnv(Env, Name, Actuals, E1, E2).                                                


%% %% %% FIN CODE (Francis Lalonde)

%% apply(+Fun, +Arg, -Val)
%% Evaluation des fonctions et des opérateurs prédéfinis.
apply(closure(X, Env, Body), Arg, V) :- eval([(X, _, Arg)|Env], Body, V).
apply(builtin(BI), Arg, V) :- builtin(BI, Arg, V).
%% builtin(list, V, list(V)).
builtin(macro, V, macro(V)).
builtin(compoundp, V, Res) :- compound(V) -> Res = true; Res = false.
builtin(makenode, Head, builtin(makenode(Head))) :- atom(Head).
builtin(makenode(Head), Args, V) :- V =.. [Head|Args].
builtin((+), N1, builtin(+(N1))).
builtin(+(N1), N2, N) :- N is N1 + N2.
builtin(car, [X|_], X).
builtin(cdr, [_|XS], XS).
builtin(cdr, [], []).
builtin(empty, X, Res) :- X = [] -> Res = true; Res = false.
builtin(cons, X, builtin(cons(X))).
builtin(cons(X), XS, [X|XS]).

%% eval(+Env, +Exp, -Val)
%% Évalue Exp dans le context Env et renvoie sa valeur Val.
eval(_, N, N) :- number(N), !.
eval(Env, X, V) :-
    atom(X), !,
    (lookup(Env, X, _, V), !;
     print_message(error, unknown_variable(X)), fail).
eval(_, quote(V), V) :- !.
eval(Env, fn(X, E), closure(X, Env, E)) :- !.
eval(Env, tfn(_, E), V) :- !, eval(Env, E, V).
eval(Env, tapp(E, _), V) :- !, eval(Env, E, V).
eval(Env, if(E1, E2, E3), V) :-
    !, eval(Env, E1, V1),
    (V1 = true -> eval(Env, E2, V);
     eval(Env, E3, V)).
eval(Env, app(E1, E2), V) :-
    !, eval(Env, E1, V1),
    eval(Env, E2, V2),
    apply(V1, V2, V).
eval(_, E, _) :-
    print_message(error, unknown_expression(E)), fail.

%% env0(-Env)
%% Renvoie l'environnment initial qui défini les types des primitives
%% implémentées directement dans le langage et son évaluateur.
env0(Env) :-
    Env = [(type, type, type),
           (sexp, type, sexp),
           (int, type, int),
           ((+), (int -> int -> int), builtin(+)),
           (bool, type, bool),
           (true, bool, true),
           (false, bool, false),
           (compoundp, (sexp -> bool), builtin(compoundp)),
           (makenode, (sexp -> list(sexp) -> sexp), builtin(makenode)),
           (nil, forall(t, list(t)), []),
           (cons, forall(t, (t -> list(t) -> list(t))), builtin(cons)),
           (empty, forall(t, (list(t) -> bool)), builtin(empty)),
           (car, forall(t, (list(t) -> t)), builtin(car)),
           (cdr, forall(t, (list(t) -> list(t))), builtin(cdr)),
           (macroexpander, type, macroexpander),
           (macro, ((list(sexp) -> sexp) -> macroexpander), builtin(macro))].

%% pervasive(-Decls)
%% Renvoie un exemple de déclarations.
pervasive(
        [define(zero, 0),
         define(zero_0, app(app(+, zero), zero)),
         define(id_int, fn(i, app(app(+, i), zero))),
         define(zero_1, app(id_int, zero)),
         %identity : forall(t, (t -> t)),
         define(identity, tfn(t, fn(x,x))),
         define(zero_2, identity(zero)),
         %% Pour pouvoir écrire "mklist(1,2,3)".
         define(mklist,
                macro(fn(args,
                         makenode(quote(cons),
                                  cons(car(args),
                                       cons(if(empty(cdr(args)),
                                               quote(nil),
                                               makenode(quote(mklist),
                                                        cdr(args))),
                                            nil)))))),
         %% Pas aussi pratique que quasiquote/unquote, mais quand même
         %% un peu mieux que just "makenode".
         define(makeqnode,
                macro(fn(args,
                         makenode(quote(makenode),
                                  mklist(makenode(quote(quote),
                                                  mklist(car(args))),
                                         makenode(quote(mklist),
                                                  cdr(args))))))),
         %% Pour pouvoir définir ses macros avec "defmacro(name,args,e)".
         define(defmacro,
                macro(fn(args,
                         makeqnode(define,
                                   car(args),
                                   makeqnode(macro,
                                             makenode(quote(fn),
                                                      cdr(args))))))),
         %% Pour pouvoir définir ses variables avec "X = E" plutôt qu'avec
         %% "define".
         defmacro(=, args, makenode(quote(define),args)),
         %% Les déclarations offrent un sorte de "let" récursif global,
         %% et cette macro-ci offre un "let(x,e1,e2)" pour ajouter une
         %% déclaration locale.
         defmacro(let, args,
                  makeqnode(app,
                            makeqnode(fn, car(args), car(cdr(cdr(args)))),
                            car(cdr(args)))),
         %% Notre bonne vieille fonction "map", qui a besoin d'une
         %% déclaration de type, vu qu'elle est récursive.
         map : forall(a, forall(b, ((a -> b) -> list(a) -> list(b)))),
         map = tfn(a, tfn(b, fn(f, fn(xs,
                                      if(empty(xs),
                                         nil,
                                         cons(f(car(xs)), map(f,cdr(xs)))))))),
         list1 = mklist(mklist(1,2,3), mklist(4,5,6), mklist(7,8,9)),
         list2 = (map(cdr,list1)),
         identity(list2)
    ]).


%%petit environnement de test
ptest([ identity : forall(t, (t -> t)),
         define(identity, tfn(t, fn(x,x))),

define(mklist,
                macro(fn(args,
                         makenode(quote(cons),
                                  cons(car(args),
                                       cons(if(empty(cdr(args)),
                                               quote(nil),
                                               makenode(quote(mklist),
                                                        cdr(args))),
                                            nil)))))),

%%         define(test_wrong, app(app(+,1),true)),
%%         +(1,41) %retourne 42
%%           f1(1) % retourne V = 1.
%%         f2(1,2,3) % retourne V = 2.

	    %mklist(1,2,3),
	    %cons(1, cons(2, nil)),
	    %cons(1, nil),
	    %(cons(nil, (cons(cons(cons(cons(cons(cons(cons(cons(cons(cons(3, nil), nil), nil), nil), nil), nil), nil), nil), nil), nil)))),
	    %app(app(tapp(cons,blah),1),tapp(nil,int)),
        
         %(map(cdr,list1))
         identity(1)
         %test_wrong
                ]).
runptest(P, V) :- env0(Env), ptest(Per), append(Per, P, Code),
             eval_decls(Env, Code, V).

%% runraw(+Prog, -Val)
%% Exécute programme Prog dans l'environnement initial.
runraw(P, V) :- env0(Env), eval_decls(Env, P, V).

%% run(+Prog, -Val)
%% Comme `runraw`, mais ajoute l'environnement "pervasive" défini ci-dessus.
run(P, V) :- env0(Env), pervasive(Per), append(Per, P, Code),
             eval_decls(Env, Code, V).