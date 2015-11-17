
:- op(700, xfx, ~).

% point composition for right-branching time

compose(=, X, [X]).

compose(<, <, [<]).
compose(<, =, [<]).
compose(<, >, [<,=,>]).
compose(<, ~, [<,~]).

compose(>, <, [<,=,>,~]).
compose(>, =, [>]).
compose(>, >, [>]).
compose(>, ~, [~]).

compose(~, <, [~]).
compose(~, =, [~]).
compose(~, >, [>,~]).
compose(~, ~, [<,=,>,~]).

% implicit: x_l < x_r, y_l < y_r

rels_to_points(rel(I1,Rels,I2), List) :-
	rels_list_to_points(Rels, I1, I2, List).

rels_list_to_points([], _, _, []).
rels_list_to_points([R|Rs], I1, I2, [L|Lists]) :-
	rel_to_point(rel(I1,R,I2), L0),
	sort([I1-l<I1-r,I2-l<I2-r|L0], L),
	rels_list_to_points(Rs, I1, I2, Lists).

rel_to_point(rel(X,<,Y), [X-r<Y-l]). % x_l < x_r, x_r < y_l, y_l < y_r
rel_to_point(rel(X,b,Y), [X-r<Y-l]). % x_l < x_r, x_r < y_l, y_l < y_r
rel_to_point(rel(Y,bi,X), [X-r<Y-l]).
rel_to_point(rel(Y,>,X), [X-r<Y-l]).
rel_to_point(rel(X,m,Y), [X-r=Y-l]).
rel_to_point(rel(Y,mi,X), [X-r=Y-l]).
rel_to_point(rel(X,o,Y), [X-l<Y-l,Y-l<X-r,X-r<Y-r]).
rel_to_point(rel(Y,oi,X), [X-l<Y-l,Y-l<X-r,X-r<Y-r]).
rel_to_point(rel(X,s,Y), [X-l=Y-l,X-r<Y-r]).
rel_to_point(rel(Y,si,X), [X-l=Y-l,X-r<Y-r]).
rel_to_point(rel(X,d,Y), [Y-l<X-l,X-r<Y-r]).
rel_to_point(rel(Y,di,X), [Y-l<X-l,X-r<Y-r]).
rel_to_point(rel(X,f,Y), [Y-l<X-l,X-r=Y-r]).
rel_to_point(rel(Y,fi,X), [Y-l<X-l,X-r=Y-r]).
rel_to_point(rel(X,e,Y), [X-l=Y-l,Y-r=Y-r]).
rel_to_point(rel(X,=,Y), [X-l=Y-l,Y-r=Y-r]).
rel_to_point(rel(X,~,Y), [X-l~Y-l]). % implies X-r~Y-r
rel_to_point(rel(X,rb,Y), [X-l<Y-l,Y-l~X-r]).
rel_to_point(rel(Y,rbi,X), [X-l<Y-l,Y-l~X-r]).
rel_to_point(rel(X,ro,Y), [X-l<Y-l,X-r~Y-r]).
rel_to_point(rel(Y,roi,X), [X-l<Y-l,X-r~Y-r]).
rel_to_point(rel(X,rs,Y), [X-l=Y-l,X-r~Y-r]).


points_to_graph(Rels, Graph) :-
	points_to_graph(Rels, [], Graph).

points_to_graph([], Graph, Graph).
points_to_graph([Rel|Rels], Graph0, Graph) :-
	points_to_graph1(Rel, Graph0, Graph1),
	points_to_graph(Rels, Graph1, Graph).


points_to_graph1([], Graph, Graph).
points_to_graph1([Rel|Rels], Graph0, Graph) :-
	points_rel_to_graph(Rel, Graph0, Graph1),
	points_to_graph1(Rels, Graph1, Graph).	

points_rel_to_graph(X<Y, Graph0, Graph) :-
	keysort([X-[Y-[<]],Y-[X-[>]]], New),
	ord_key_key_union(Graph0, New, Graph).
points_rel_to_graph(X>Y, Graph0, Graph) :-
	keysort([X-[Y-[>]],Y-[X-[<]]], New),
	ord_key_union(Graph0, New, Graph).
points_rel_to_graph(X=Y, Graph0, Graph) :-
	keysort([X-[Y-[=]],Y-[X-[=]]], New),
	ord_key_union(Graph0, New, Graph).
points_rel_to_graph(X~Y, Graph0, Graph) :-
	keysort([X-[Y-[~]],Y-[X-[~]]], New),
	ord_key_union(Graph0, New, Graph).


neighbors(V, [V0-Neighbors|_], Neighbors) :-
	V0==V,
	!.
neighbors(V, [_|Graph], Neighbors) :-
	neighbors(V, Graph, Neighbors).


warshall(Graph, Closure) :-
	warshall(Graph, Graph, Closure).

warshall([], Closure, Closure).
warshall([V-_|G], E, Closure) :-
	neighbors(V, E, Y),
	warshall(E, V, Y, NewE),
	warshall(G, NewE, Closure).

warshall([], _, _, []).
warshall([X-Neibs|G], V, Y, [X-NewNeibs|NewG]) :-
	ord_key_member(V, Neibs, _),
	!,
	ord_key_union_c(Neibs, Y, NewNeibs),
	warshall(G, V, Y, NewG).
warshall([X-Neibs|G], V, Y, [X-Neibs|NewG]) :-
	warshall(G, V, Y, NewG).



% = ord_key_union_c(+Map1, +Map2, ?Map3)
%
% as ord_union/3, but for ordered sets of Key-Value pairs, where Value
% is itself an ordered set. If Map1 and Map2 contain the same Key,
% Map3 will contain the ord_union of the two values.                RM

ord_key_union_c([], Set2, Set2).
ord_key_union_c([H1-V1|T1], Set2, Union) :-
	ord_key_union_c_2(Set2, H1, V1, T1, Union).

ord_key_union_c_2([], H1, V1, T1, [H1-V1|T1]).
ord_key_union_c_2([H2-V2|T2], H1, V1, T1, Union) :-
	compare(Order, H1, H2),
	ord_key_union_c_3(Order, H1, V1, T1, H2, V2, T2, Union).

ord_key_union_c_3(<, H1, V1, T1, H2, V2, T2, [H1-V1|Union]) :-
	ord_key_union_c_2(T1, H2, V2, T2, Union).
ord_key_union_c_3(=, H1, V1, T1, _, V2, T2, [H1-V|Union]) :-
	setof(X, (member(R1,V1),member(R2,V2),compose(R1,R2,V3),member(X,V3)), V),
%	ord_union_c(V1, V2, V),
	ord_key_union_c(T1, T2, Union).
ord_key_union_c_3(>, H1, V1, T1, H2, V2, T2, [H2-V2|Union]) :-
	ord_key_union_c_2(T2, H1, V1, T1, Union).


% = ord_key_key_union(+Map1, +Map2, ?Map3)
%
% as ord_union/3, but for ordered sets of Key-Value pairs, where Value
% is itself an ordered set. If Map1 and Map2 contain the same Key,
% Map3 will contain the ord_union of the two values.                RM

ord_key_key_union([], Set2, Set2).
ord_key_key_union([H1-V1|T1], Set2, Union) :-
	ord_key_key_union_2(Set2, H1, V1, T1, Union).

ord_key_key_union_2([], H1, V1, T1, [H1-V1|T1]).
ord_key_key_union_2([H2-V2|T2], H1, V1, T1, Union) :-
	compare(Order, H1, H2),
	ord_key_union_3(Order, H1, V1, T1, H2, V2, T2, Union).

ord_key_key_union_3(<, H1, V1, T1, H2, V2, T2, [H1-V1|Union]) :-
	ord_key_key_union_2(T1, H2, V2, T2, Union).
ord_key_key_union_3(=, H1, V1, T1, _, V2, T2, [H1-V|Union]) :-
	ord_key_union(V1, V2, V),
	ord_key_key_union(T1, T2, Union).
ord_key_key_union_3(>, H1, V1, T1, H2, V2, T2, [H2-V2|Union]) :-
	ord_key_key_union_2(T2, H1, V1, T1, Union).


% = ord_key_union(+Map1, +Map2, ?Map3)
%
% as ord_union/3, but for ordered sets of Key-Value pairs, where Value
% is itself an ordered set. If Map1 and Map2 contain the same Key,
% Map3 will contain the ord_union of the two values.                RM

ord_key_union([], Set2, Set2).
ord_key_union([H1-V1|T1], Set2, Union) :-
	ord_key_union_2(Set2, H1, V1, T1, Union).

ord_key_union_2([], H1, V1, T1, [H1-V1|T1]).
ord_key_union_2([H2-V2|T2], H1, V1, T1, Union) :-
	compare(Order, H1, H2),
	ord_key_union_3(Order, H1, V1, T1, H2, V2, T2, Union).

ord_key_union_3(<, H1, V1, T1, H2, V2, T2, [H1-V1|Union]) :-
	ord_key_union_2(T1, H2, V2, T2, Union).
ord_key_union_3(=, H1, V1, T1, _, V2, T2, [H1-V|Union]) :-
	ord_union(V1, V2, V),
	ord_key_union(T1, T2, Union).
ord_key_union_3(>, H1, V1, T1, H2, V2, T2, [H2-V2|Union]) :-
	ord_key_union_2(T2, H1, V1, T1, Union).

%   ord_union(+Set1, +Set2, ?Union)
%   is true when Union is the union of Set1 and Set2.  Note that when
%   something occurs in both sets, we want to retain only one copy.

%   replaced original code with improved code from Richard A. O'Keefe's
%   `The Craft of Prolog' (1990) MIT Press. Read this book for discussion
%   and comments on the code.                                          RM

ord_union([], Set2, Set2).
ord_union([H1|T1], Set2, Union) :-
	ord_union_2(Set2, H1, T1, Union).

ord_union_2([], H1, T1, [H1|T1]).
ord_union_2([H2|T2], H1, T1, Union) :-
	compare(Order, H1, H2),
	ord_union_3(Order, H1, T1, H2, T2, Union).

ord_union_3(<, H1, T1, H2, T2, [H1|Union]) :-
	ord_union_2(T1, H2, T2, Union).
ord_union_3(=, H1, T1, _, T2, [H1|Union]) :-
	ord_union(T1, T2, Union).
ord_union_3(>, H1, T1, H2, T2, [H2|Union]) :-
	ord_union_2(T2, H1, T1, Union).


% = ord_key_member(+Key, +OrdSet, ?Value)
%
% as ord_member/2, but assumes the elements of OrdSet are Key-Value
% pairs.                                                            RM

ord_key_member(Element, [Head-Data0|Tail], Data) :-
	compare(Order, Element, Head),
	ord_key_member(Order, Element, Tail, Data0, Data).

ord_key_member(=, _, _, Data, Data).
ord_key_member(>, Element, Tail, _, Data) :-
	ord_key_member(Element, Tail, Data).
% = ord_key_intersect(+Map1, +Map2, ?Map3)
%
% as ord_intersect/3, but for ordered sets of Key-Value pairs, where
% Value is itself an ordered set. If Map1 and Map2 contain the same Key,
% Map3 will contain the ord_intersect of the two values.              RM

ord_key_intersect([], _, []).
ord_key_intersect([H1-V1|T1], Set2, Intersection) :-
	ord_key_intersect_2(Set2, H1, V1, T1, Intersection).

ord_key_intersect_2([], _, _, _, []).
ord_key_intersect_2([H2-V2|T2], H1, V1, T1, Intersection) :-
	compare(Order, H1, H2),
	ord_key_intersect_3(Order, H1, V1, T1, H2, V2, T2, Intersection).

ord_key_intersect_3(<, _, _, T1, H2, V2, T2, Intersection) :-
	ord_key_intersect_2(T1, H2, V2, T2, Intersection).
ord_key_intersect_3(=, H1, V1, T1, _, V2, T2, [H1-V|Intersection]) :-
	ord_intersect(V1, V2, V),
	ord_key_intersect(T1, T2, Intersection).
ord_key_intersect_3(>, H1, V1, T1, _, _, T2, Intersection) :-
	ord_key_intersect_2(T2, H1, V1, T1, Intersection).

% = ord_key_union_i(+Map1, +Map2, ?Map3)
%
% as ord_union/3, but for ordered sets of Key-Value pairs, where Value
% is itself an ordered set. If Map1 and Map2 contain the same Key,
% Map3 will contain the ord_interset of the two values.             RM

ord_key_union_i([], Set2, Set2).
ord_key_union_i([H1-V1|T1], Set2, Union) :-
	ord_key_union_i2(Set2, H1, V1, T1, Union).

ord_key_union_i2([], H1, V1, T1, [H1-V1|T1]).
ord_key_union_i2([H2-V2|T2], H1, V1, T1, Union) :-
	compare(Order, H1, H2),
	ord_key_union_i3(Order, H1, V1, T1, H2, V2, T2, Union).

ord_key_union_i3(<, H1, V1, T1, H2, V2, T2, [H1-V1|Union]) :-
	ord_key_union_i2(T1, H2, V2, T2, Union).
ord_key_union_i3(=, H1, V1, T1, _, V2, T2, [H1-V|Union]) :-
	ord_intersect(V1, V2, V),
	ord_key_union_i(T1, T2, Union).
ord_key_union_i3(>, H1, V1, T1, H2, V2, T2, [H2-V2|Union]) :-
	ord_key_union_i2(T2, H1, V1, T1, Union).


%   ord_intersect(+Set1, +Set2, ?Intersection)
%   is true when Intersection is the ordered representation of Set1
%   and Set2, provided that Set1 and Set2 are ordered sets.

%   modified to work without cuts, like ord_union/3     20040429 RM
%   removed error in the base case                      20040503 RM

ord_intersect([], _, []).
ord_intersect([H1|T1], Set2, Intersection) :-
	ord_intersect_2(Set2, H1, T1, Intersection).

ord_intersect_2([], _, _, []).
ord_intersect_2([H2|T2], H1, T1, Intersection) :-
	compare(Order, H1, H2),
	ord_intersect_3(Order, H1, T1, H2, T2, Intersection).

ord_intersect_3(<, _, T1, H2, T2, Intersection) :-
	ord_intersect_2(T1, H2, T2, Intersection).
ord_intersect_3(=, H1, T1, _, T2, [H1|Intersection]) :-
	ord_intersect(T1, T2, Intersection).
ord_intersect_3(>, H1, T1, _, T2, Intersection) :-
	ord_intersect_2(T2, H1, T1, Intersection).
