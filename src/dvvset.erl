%% coding: latin-1

%%%-------------------------------------------------------------------
%%%
%%% File:      dvvset.erl
%%%
%%% @title Dotted Version Vector Set
%%% @author    Ricardo Tom� Gon�alves <tome.wave@gmail.com>
%%% @author    Paulo S�rgio Almeida <pssalmeida@gmail.com>
%%%
%%% @copyright The MIT License (MIT)
%%% Copyright (C) 2013
%%%
%%% Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
%%%
%%% The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
%%%
%%% THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
%%%
%%% @doc  
%%% An Erlang implementation of *compact* Dotted Version Vectors, which
%%% provides a container for a set of concurrent values (siblings) with causal
%%% order information.
%%%
%%% For further reading, visit the <a href="https://github.com/ricardobcl/Dotted-Version-Vectors">github page</a>.
%%% @end  
%%%
%%% @reference
%%% <a href="http://arxiv.org/abs/1011.5808">
%%% Dotted Version Vectors: Logical Clocks for Optimistic Replication
%%% </a>
%%% @end
%%%
%%%-------------------------------------------------------------------

-module(dvvset).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

-export([new/1,
         new/2,
         new_list/1,
         new_list/2,
         sync/1,
         join/1,
         update/2,
         update/3,
         size/1,
         ids/1,
         values/1,
         equal/2,
         less/2,
         map/2,
         last/2,
         lww/2,
         reconcile/2
        ]).

-export_type([clock/0, vector/0, id/0, value/0]).

% % @doc
%% STRUCTURE details:
%%      * entries() are sorted by id()
%%      * each counter() also includes the number of values in that id()
%%      * the values in each triple of entries() are causally ordered and each new value goes to the head of the list

-type clock()   :: {entries(), values()}.
-type vector()  :: [{id(), counter()}].
-type entries() :: [{id(), counter(), values()}].
-type id()      :: any().
-type values()  :: [value()].
-type value()   :: any().
-type counter() :: non_neg_integer().


%% @doc Constructs a new clock set without causal history,
%% and receives one value that goes to the anonymous list.
-spec new(value()) -> clock().
new(Value) -> {[], [Value]}.

%% @doc Same as new/1, but receives a list of values, instead of a single value.
-spec new_list([value()]) -> clock().
new_list(Values) when is_list(Values) -> {[], Values};
new_list(Value) -> {[], [Value]}.

%% @doc Constructs a new clock set with the causal history
%% of the given version vector / vector clock,
%% and receives one value that goes to the anonymous list.
%% The version vector SHOULD BE the output of join/1.
-spec new(vector(), value()) -> clock().
new(VV, Value) ->
    VVS = lists:sort(VV), % defense against non-order preserving serialization
    {[{Id, Counter, []} || {Id, Counter} <- VVS], [Value]}.

%% @doc Same as new/2, but receives a list of values, instead of a single value.
-spec new_list(vector(), [value()]) -> clock().
new_list(VV, Values) when is_list(Values) ->
    VVS = lists:sort(VV), % defense against non-order preserving serialization
    {[{Id, Counter, []} || {Id, Counter} <- VVS], Values};
new_list(VV, Value) -> new_list(VV, [Value]).

%% @doc Synchronizes a list of clocks using sync/2.
%% It discards (causally) outdated values, 
%% while merging all causal histories.
-spec sync([clock()]) -> clock().
sync(ListClocks) -> lists:foldl(fun sync/2, {}, ListClocks).

%% Private function
-spec sync(clock(), clock()) -> clock().
sync({}, Clock) -> Clock;
sync(Clock ,{}) -> Clock;
sync(Clock1={Entries1,Values1},Clock2={Entries2,Values2}) ->
    Value = case less(Clock1,Clock2) of
        true  -> Values2; % Clock1 < Clock2 => return Values2
        false -> case less(Clock2,Clock1) of
                    true  -> Values1; % Clock2 < Clock1 => return Values1
                    false -> % keep all unique anonymous values and sync entries()
                        sets:to_list(sets:from_list(Values1++Values2))
                 end
    end,
    {sync2(Entries1,Entries2),Value}.

%% Private function
-spec sync2(entries(), entries()) -> entries().
sync2([], Clock) -> Clock;
sync2(Clock, []) -> Clock;
sync2([{Id1, Counter1, Values1}=H1 | Entries1]=Clock1, [{Id2, Counter2, Values2}=H2 | Entries2]=Clock2) ->
    if
      Id1 < Id2 -> [H1 | sync2(Entries1, Clock2)];
      Id1 > Id2 -> [H2 | sync2(Entries2, Clock1)];
      true    -> [merge(Id1, Counter1, Values1, Counter2, Values2) | sync2(Entries1, Entries2)]
    end.

%% Private function
-spec merge(id(), counter(), values(), counter(), values()) -> {id(), counter(), values()}.
merge(Id, Counter1, Values1, Counter2, Values2) ->
    LL1 = length(Values1),
    LL2 = length(Values2),
    case Counter1 >= Counter2 of
        true ->
          case Counter1 - LL1 >=  Counter2 - LL2 of 
            true  -> {Id, Counter1, Values1};
            false -> {Id, Counter1, lists:sublist(Values1, Counter1 - Counter2 + LL2)}
          end;
        false ->
          case Counter2 - LL2 >=  Counter1 - LL1 of 
            true  -> {Id, Counter2, Values2};
            false -> {Id, Counter2, lists:sublist(Values2, Counter2 - Counter1 + LL1)}
          end
    end.


%% @doc Return a version vector that represents the causal history.
-spec join(clock()) -> vector().
join({Clock,_}) -> [{Id, Counter} || {Id, Counter, _} <- Clock].

%% @doc Advances the causal history with the given id.
%% The new value is the *anonymous dot* of the clock.
%% The client clock SHOULD BE a direct result of new/2.
-spec update(clock(), id()) -> clock().
update({Clock,[Value]}, Id) -> {event(Clock, Id, Value), []}.

%% @doc Advances the causal history of the
%% first clock with the given id, while synchronizing
%% with the second clock, thus the new clock is
%% causally newer than both clocks in the argument.
%% The new value is the *anonymous dot* of the clock.
%% The first clock SHOULD BE a direct result of new/2,
%% which is intended to be the client clock with
%% the new value in the *anonymous dot* while
%% the second clock is from the local server.
-spec update(clock(), clock(), id()) -> clock().
update({Cc,[Value]}, Cr, Id) ->
    %% Sync both clocks without the new value
    {Clock,Values} = sync({Cc,[]}, Cr),
    %% We create a new event on the synced causal history,
    %% with the id Id and the new value.
    %% The anonymous values that were synced still remain.
    {event(Clock, Id, Value), Values}.

%% Private function
-spec event(vector(), id(), value()) -> entries().
event([], Id, Value) -> [{Id, 1, [Value]}];
event([{Id, Counter, ListClocks} | T], Id, Value) -> [{Id, Counter+1, [Value | ListClocks]} | T];
event([{Id1, _, _} | _]=Clock, Id, Value) when Id1 > Id -> [{Id, 1, [Value]} | Clock];
event([H | T], Id, Value) -> [H | event(T, Id, Value)].

%% @doc Returns the total number of values in this clock set.
-spec size(clock()) -> non_neg_integer().
size({Clock,Values}) -> lists:sum([length(ListClocks) || {_,_,ListClocks} <- Clock]) + length(Values).

%% @doc Returns all the ids used in this clock set.
-spec ids(clock()) -> [id()].
ids({Clock,_}) -> ([Id || {Id,_,_} <- Clock]).

%% @doc Returns all the values used in this clock set,
%% including the anonymous values.
-spec values(clock()) -> [value()].
values({Clock,Values}) -> Values ++ lists:append([ListClocks || {_,_,ListClocks} <- Clock]).

%% @doc Compares the equality of both clocks, regarding
%% only the causal histories, thus ignoring the values.
-spec equal(clock() | vector(), clock() | vector()) -> boolean().
equal({Clock1,_},{Clock2,_}) -> equal2(Clock1,Clock2); % DVVSet
equal(Clock1,Clock2) when is_list(Clock1) and is_list(Clock2) -> equal2(Clock1,Clock2). %vector clocks

%% Private function
-spec equal2(vector(), vector()) -> boolean().
equal2([], []) -> true;
equal2([{Id, Clock, Values1} | Entries1], [{Id, Clock, Values2} | Entries2]) 
    when length(Values1) =:= length(Values2) -> 
    equal2(Entries1, Entries2);
equal2(_, _) -> false.

%% @doc Returns True if the first clock is causally older than
%% the second clock, thus values on the first clock are outdated.
%% Returns False otherwise.
-spec less(clock(), clock()) -> boolean().
less({Clock1,_}, {Clock2,_}) -> greater(Clock2, Clock1, false).

%% Private function
-spec greater(vector(), vector(), boolean()) -> boolean().
greater([], [], Strict) -> Strict;
greater([_|_], [], _) -> true;
greater([], [_|_], _) -> false;
greater([{Id, Counter1, _} | Entries1], [{Id, Counter2, _} | Entries2], Strict) ->
   if
     Counter1 == Counter2 -> greater(Entries1, Entries2, Strict);
     Counter1 >  Counter2 -> greater(Entries1, Entries2, true);
     Counter1 <  Counter2 -> false
   end;
greater([{Id1, _, _} | Entries1], [{Id2, _, _} | _]=Clock2, _) when Id1 < Id2 -> greater(Entries1, Clock2, true);
greater(_, _, _) -> false.

%% @doc Maps (applies) a function on all values in this clock set,
%% returning the same clock set with the updated values.
-spec map(fun((value()) -> value()), clock()) -> clock().
map(Function, {Clock,Values}) -> 
    {[ {Id, Counter, lists:map(Function, Value)} || {Id, Counter, Value} <- Clock], lists:map(Function, Values)}.


%% @doc Return a clock with the same causal history, but with only one
%% value in the anonymous placeholder. This value is the result of
%% the function Function, which takes all values and returns a single new value.
-spec reconcile(Winner::fun(([value()]) -> value()), clock()) -> clock().
reconcile(Function, Clock) ->
    Value = Function(values(Clock)),
    new(join(Clock), Value).

%% @doc Returns the latest value in the clock set,
%% according to function Function(A,B), which returns *true* if 
%% A compares less than or equal to B, false otherwise.
-spec last(LessOrEqual::fun((value(),value()) -> boolean()), clock()) -> value().
last(Function, Clock) ->
   {_ ,_ , Values2} = find_entry(Function, Clock),
   Values2.

%% @doc Return a clock with the same causal history, but with only one
%% value in its original position. This value is the newest value
%% in the given clock, according to function Function(A,B), which returns *true*
%% if A compares less than or equal to B, false otherwise.
-spec lww(LessOrEqual::fun((value(),value()) -> boolean()), clock()) -> clock().
lww(Function, Clock={E,_}) ->
    case find_entry(Function, Clock) of
        {id, Id, Value}      -> {join_and_replace(Id, Value, E),[]};
        {anonym, _, Value}  -> new(join(Clock), Value)
    end.

%% find_entry/2 - Private function
find_entry(Function, {[], [Value|T]}) -> find_entry(Function, null, Value, {[],T}, anonym);
find_entry(Function, {[{_, _, []} | T], Values}) -> find_entry(Function, {T,Values});
find_entry(Function, {[{Id, _, [Value|_]} | T], Values}) -> find_entry(Function, Id, Value, {T,Values}, id).

%% find_entry/5 - Private function
find_entry(Function, Id, Value, Clock, Flag) ->
    Fun = fun (A,B) ->
        case Function(A,B) of
            false -> {left,A}; % A is newer than B
            true  -> {right,B} % A is older than B
        end
    end,
    find_entry2(Fun, Id, Value, Clock, Flag).

%% find_entry2/5 - Private function
find_entry2(_, Id, Value, {[], []}, anonym) -> {anonym, Id , Value};
find_entry2(_, Id, Value, {[], []}, id) -> {id, Id, Value};
find_entry2(Function, Id, Value, {[], [Values1 | T]}, Flag) ->
    case Function(Value, Values1) of
        {left,Values2}  -> find_entry2(Function, Id, Values2, {[],T}, Flag);
        {right,Values2} -> find_entry2(Function, Id, Values2, {[],T}, anonym)
    end;
find_entry2(Function, Id, Value, {[{_, _, []} | T], Values}, Flag) -> find_entry2(Function, Id, Value, {T, Values}, Flag);
find_entry2(Function, Id, Value, {[{Id1, _, [Values1|_]} | T], Values}, Flag) -> 
    case Function(Value, Values1) of
        {left,Values2}  -> find_entry2(Function, Id, Values2, {T, Values}, Flag);
        {right,Values2} -> find_entry2(Function, Id1, Values2, {T, Values}, Flag)
    end.

%% Private function
join_and_replace(Ir, Value, Clock) -> 
    [if
       Id == Ir -> {Id, Counter, [Value]};
       true    -> {Id, Counter, []}
     end
     || {Id, Counter, _} <- Clock].


%% ===================================================================
%% EUnit tests
%% ===================================================================
-ifdef(TEST).


join_test() ->
    A  = new(v1),
    A1 = update(A,a),
    B  = new(join(A1),v2),
    B1 = update(B, A1, b),
    ?assertEqual( join(A)  , []             ),
    ?assertEqual( join(A1) , [{a,1}]        ),
    ?assertEqual( join(B1) , [{a,1},{b,1}]  ),
    ok.

update_test() ->
    A0 = update(new(v1),a),
    A1 = update(new_list(join(A0),[v2]), A0, a),
    A2 = update(new_list(join(A1),[v3]), A1, b),
    A3 = update(new_list(join(A0),[v4]), A1, b),
    A4 = update(new_list(join(A0),[v5]), A1, a),
    ?assertEqual( A0 , {[{a,1,[v1]}],[]}                ),
    ?assertEqual( A1 , {[{a,2,[v2]}],[]}                ),
    ?assertEqual( A2 , {[{a,2,[]}, {b,1,[v3]}],[]}      ),
    ?assertEqual( A3 , {[{a,2,[v2]}, {b,1,[v4]}],[]}    ),
    ?assertEqual( A4 , {[{a,3,[v5,v2]}],[]}             ),
    ok.

sync_test() ->
    X   = {[{x,1,[]}],[]},
    A   = update(new(v1),a),
    Y   = update(new_list([v2]),b),
    A1  = update(new_list(join(A),[v2]), a),
    A3  = update(new_list(join(A1),[v3]), b),
    A4  = update(new_list(join(A1),[v3]), c),
    Function   = fun (ListClocks,R) -> ListClocks>R end,
    W   = {[{a,1,[]}],[]},
    Z   = {[{a,2,[v2,v1]}],[]},
    ?assertEqual( sync([W,Z])     , {[{a,2,[v2]}],[]}                         ),
    ?assertEqual( sync([W,Z])     , sync([Z,W])                               ),
    ?assertEqual( sync([A,A1])    , sync([A1,A])                              ),
    ?assertEqual( sync([A4,A3])   , sync([A3,A4])                             ),
    ?assertEqual( sync([A4,A3])   , {[{a,2,[]}, {b,1,[v3]}, {c,1,[v3]}],[]}   ),
    ?assertEqual( sync([X,A])     , {[{a,1,[v1]},{x,1,[]}],[]}                ),
    ?assertEqual( sync([X,A])     , sync([A,X])                               ),
    ?assertEqual( sync([X,A])     , sync([A,X])                               ),
    ?assertEqual( sync([A,Y])     , {[{a,1,[v1]},{b,1,[v2]}],[]}              ),
    ?assertEqual( sync([Y,A])     , sync([A,Y])                               ),
    ?assertEqual( sync([Y,A])     , sync([A,Y])                               ),
    ?assertEqual( sync([A,X])     , sync([X,A])                               ),
    ?assertEqual( lww(Function,A4)     , sync([A4,lww(Function,A4)])                        ),
    ok.

sync_update_test() ->
    A0  = update(new_list([v1]), a),             % Mary writes v1 w/o VV
    VV1 = join(A0),                              % Peter reads v1 with version vector (VV)
    A1  = update(new_list([v2]), A0, a),         % Mary writes v2 w/o VV
    A2  = update(new_list(VV1,[v3]), A1, a),     % Peter writes v3 with VV from v1
    ?assertEqual( VV1 , [{a,1}]                          ),
    ?assertEqual( A0  , {[{a,1,[v1]}],[]}                ),
    ?assertEqual( A1  , {[{a,2,[v2,v1]}],[]}             ),
    % now A2 should only have v2 and v3, since v3 was causally newer than v1
    ?assertEqual( A2  , {[{a,3,[v3,v2]}],[]}             ),
    ok.

event_test() ->
    {A,_} = update(new(v1),a),
    ?assertEqual( event(A,a,v2) , [{a,2,[v2,v1]}]           ),
    ?assertEqual( event(A,b,v2) , [{a,1,[v1]}, {b,1,[v2]}]  ),
    ok.

lww_last_test() ->
    Function  = fun (A,B) -> A =< B end,
    F2 = fun ({_,TS1}, {_,TS2}) -> TS1 =< TS2 end,
    X  = {[{a,4,[5,2]},{b,1,[]},{c,1,[3]}],[]},
    Y  = {[{a,4,[5,2]},{b,1,[]},{c,1,[3]}],[10,0]},
    Z  = {[{a,4,[5,2]}, {b,1,[1]}], [3]},
    A  = {[{a,4,[{5, 1002345}, {7, 1002340}]}, {b,1,[{4, 1001340}]}], [{2, 1001140}]},
    ?assertEqual( last(Function,X) , 5                                         ),
    ?assertEqual( last(Function,Y) , 10                                        ),
    ?assertEqual( lww(Function,X)  , {[{a,4,[5]},{b,1,[]},{c,1,[]}],[]}        ),
    ?assertEqual( lww(Function,Y)  , {[{a,4,[]},{b,1,[]},{c,1,[]}],[10]}       ),
    ?assertEqual( lww(Function,Z)  , {[{a,4,[5]},{b,1,[]}],[]}                 ),
    ?assertEqual( lww(F2,A) , {[{a,4,[{5, 1002345}]}, {b,1,[]}], []}    ),
    ok.

reconcile_test() ->
    F1 = fun (ListClocks) -> lists:sum(ListClocks) end,
    F2 = fun (ListClocks) -> hd(lists:sort(ListClocks)) end,
    X  = {[{a,4,[5,2]},{b,1,[]},{c,1,[3]}],[]},
    Y  = {[{a,4,[5,2]},{b,1,[]},{c,1,[3]}],[10,0]},
    ?assertEqual( reconcile(F1,X) , {[{a,4,[]},{b,1,[]},{c,1,[]}],[10]} ),
    ?assertEqual( reconcile(F1,Y) , {[{a,4,[]},{b,1,[]},{c,1,[]}],[20]} ),
    ?assertEqual( reconcile(F2,X) , {[{a,4,[]},{b,1,[]},{c,1,[]}],[2]}  ),
    ?assertEqual( reconcile(F2,Y) , {[{a,4,[]},{b,1,[]},{c,1,[]}],[0]}  ),
    ok.

less_test() ->
    A  = update(new_list(v1),[a]),
    B  = update(new_list(join(A),[v2]), a),
    B2 = update(new_list(join(A),[v2]), b),
    B3 = update(new_list(join(A),[v2]), z),
    Clock  = update(new_list(join(B),[v3]), A, c),
    D  = update(new_list(join(Clock),[v4]), B2, d),
    ?assert(    less(A,B)  ),
    ?assert(    less(A,Clock)  ),
    ?assert(    less(B,Clock)  ),
    ?assert(    less(B,D)  ),
    ?assert(    less(B2,D) ),
    ?assert(    less(A,D)  ),
    ?assertNot( less(B2,Clock) ),
    ?assertNot( less(B,B2) ),
    ?assertNot( less(B2,B) ),
    ?assertNot( less(A,A)  ),
    ?assertNot( less(Clock,Clock)  ),
    ?assertNot( less(D,B2) ),
    ?assertNot( less(B3,D) ),
    ok.

equal_test() ->
    A = {[{a,4,[v5,v0]},{b,0,[]},{c,1,[v3]}], [v0]},
    B = {[{a,4,[v555,v0]}, {b,0,[]}, {c,1,[v3]}], []},
    Clock = {[{a,4,[v5,v0]},{b,0,[]}], [v6,v1]},
    % compare only the causal history
    ?assert(    equal(A,B) ),
    ?assert(    equal(B,A) ),
    ?assertNot( equal(A,Clock) ),
    ?assertNot( equal(B,Clock) ),
    ok.

size_test() ->
    ?assertEqual( 1 , ?MODULE:size(new_list([v1]))                                       ),
    ?assertEqual( 5 , ?MODULE:size({[{a,4,[v5,v0]},{b,0,[]},{c,1,[v3]}],[v4,v1]})   ),
    ok.

ids_values_test() ->
    A = {[{a,4,[v0,v5]},{b,0,[]},{c,1,[v3]}], [v1]},
    B = {[{a,4,[v0,v555]}, {b,0,[]}, {c,1,[v3]}], []},
    Clock = {[{a,4,[]},{b,0,[]}], [v1,v6]},
    ?assertEqual( ids(A)                , [a,b,c]       ),
    ?assertEqual( ids(B)                , [a,b,c]       ),
    ?assertEqual( ids(Clock)                , [a,b]         ),
    ?assertEqual( lists:sort(values(A)) , [v0,v1,v3,v5] ),
    ?assertEqual( lists:sort(values(B)) , [v0,v3,v555]  ),
    ?assertEqual( lists:sort(values(Clock)) , [v1,v6]       ),
    ok.

map_test() ->
    A = {[{a,4,[]},{b,0,[]},{c,1,[]}],[10]},
    B = {[{a,4,[5,0]},{b,0,[]},{c,1,[2]}],[20,10]},
    Function = fun (X) -> X*2 end,
    ?assertEqual( map(Function,A) , {[{a,4,[]},{b,0,[]},{c,1,[]}],[20]}            ),
    ?assertEqual( map(Function,B) , {[{a,4,[10,0]},{b,0,[]},{c,1,[4]}],[40,20]}    ),
    ok.

-endif.
