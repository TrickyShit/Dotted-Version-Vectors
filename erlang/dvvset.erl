
%%%-------------------------------------------------------------------
%%%
%%% File:      dvvset.erl
%%%
%%% @author    Ricardo Tom� Gon�alves <tome.wave@gmail.com>
%%% @author    Paulo S�rgio Almeida <pssalmeida@gmail.com>
%%%
%%% This file is provided to you under the Apache License,
%%% Version 2.0 (the "License"); you may not use this file
%%% except in compliance with the License.  You may obtain
%%% a copy of the License at
%%%
%%%   http://www.apache.org/licenses/LICENSE-2.0
%%%
%%% Unless required by applicable law or agreed to in writing,
%%% software distributed under the License is distributed on an
%%% "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
%%% KIND, either express or implied.  See the License for the
%%% specific language governing permissions and limitations
%%% under the License.
%%%
%%% @doc  
%%% An Erlang implementation of *compact* Dotted Version Vectors, which
%%% provides a container for a set of concurrent values (siblings) with causal
%%% order information.
%%% Some functions were adapted from the vclock.erl file (for Version Vectors) of Basho's Riak.
%%%
%%% This file represents the data structure *clock()*. We can use this to keep a value and its causal history, with the support for multiples values if they are causally conflicting. The clock() is supposed to have 1 value, unless we synchronize or update 2 conflicting clocks (we cannot decide through their causal history, which one is newer).
%%% Therefore, this data structure abstracts the process of tracking and reasoning about the causal relationship of multiple values.
%%%
%%% The main use case in which this was thought is a server-client system like a database. For this, the common usage of our clock() is the following:
%%%
%%% 1 - A new value V from the client -> 
%%%      -- create a new clock() for the value using C = new(V);
%%%      -- update the causal history of C using the server ID using update(C, serverID);
%%%
%%% 2 - A read from the client -> 
%%%      -- synchronize different server clocks using C = sync("list of clocks");
%%%      -- return the value(s) using values(C) and an opaque version vector using join(C);
%%%
%%% 3 - A write from the client with an updated V and an opaque (unaltered) version vector VV (obtained from a previous read on this key) ->
%%%      -- create a new clock() for the value using C = new(VV, V);
%%%      -- update the causal history of C using the server ID, and the local server clock() Cs using update(C, Cs, serverID);
%%%
%%% 4 - A coordinator of a write sends to a replica the new clock() C to synchronize locally ->
%%%      -- the new clock() C and the local clock() Cr must be reconciled into 1 clock() using C2 = sync(C, Cr), which discards causally outdated values and merges the causal history of both C and Cr, and save locally the clock() C2.
%%%
%%% 5 - An anti-entropy synchronization between 2 replicas ->
%%%      -- the local replica should test if the local clock() C is causally newer than the remote clock() Cr, using less(Cr,C). If less(Cr,C) is true, then we already have the newest clock() so do nothing. Otherwise, we should do C2 = sync(C,Cr) to reconcile both clocks and write locally the resulting clock() C2.
%%%
%%% 6 - A client writes a value V but does not care for conflicts, thus the last value should always win a conflict and be written (a technique often called last-write-wins or lww) ->
%%%      -- the server does a normal write (as in step 3), but with the resulting clock() C, we should use C2 = lww(F,C), where F is a function that compares two values F(A,B) and returns true if A wins, or false otherwise. C2 has the same causal information of C, but with only 1 value, according to F;
%%%      -- we could only do C = new(V) and write C immediately, saving the cost of a local read to do the update() + lww(), but we should preserve causal information if this lww strategy setting could be set on and off in this key lifetime;
%%%
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
         sync/1,
         sync/2,
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
         lww/2
        ]).

-export_type([clock/0, vector/0, id/0, value/0]).


%% STRUCTURE
%% Invariants:
%%      * entries() is sorted by id()
%%      * each counter() also includes the number of values in that id()
%%      * the values in each triple of entries() are causally ordered and each new value goes to the head of the list

-opaque clock() :: {entries(), values()}.
-type entries() :: [{id(), counter(), values()}].
-opaque vector() :: [{id(), counter()}].
-type id() :: any().
-type values() :: [value()].
-type value() :: any().
-type counter() :: non_neg_integer().


%% @doc Constructs a new clock set with no causal history,
%% and the new value in the anonymous list.
-spec new(value()) -> clock().
new(V) -> new([], [V]).

%% @doc Constructs a new clock set with the causal history
%% of the given version vector / vector clock,
%% and the new value in put in the anonymous list.
%% The version vector SHOULD BE a direct result of join/1.
-spec new(vector(), value()) -> clock().
new(VV, V) -> 
    VVS = lists:sort(VV), % defense against non-order preserving serialization
    {[{I, N, []} || {I, N} <- VVS], [V]}.

%% @doc Synchronizes a list of clocks using sync/2.
-spec sync([clock()]) -> clock().
sync(L) -> lists:foldl(fun sync/2, {}, L).

%% @doc Synchronizes 2 clocks.
%% Discards (causally) outdated values, while merging both causal histories.
-spec sync(clock(), clock()) -> clock().
sync({},C) -> C;
sync(C,{}) -> C;
sync(C1={E1,V1},C2={E2,V2}) ->
    case less(C1,C2) of
        true  -> C2; % C1 < C2 => return C2
        false -> case less(C2,C1) of
                    true  -> C1; % C2 < C1 => return C1
                    
                    false -> % keep all unique anonymous values and sync entries()
                        V3 = sets:to_list(sets:from_list(V1++V2)),
                        {sync2(E1,E2),V3}
                 end
    end.

%% Private function
-spec sync2(entries(), entries()) -> entries().
sync2([], C) -> C;
sync2(C, []) -> C;
sync2([{I1, N1, L1}=H1 | T1]=C1, [{I2, N2, L2}=H2 | T2]=C2) ->
    if
      I1 < I2 -> [H1 | sync2(T1, C2)];
      I1 > I2 -> [H2 | sync2(T2, C1)];
      true    -> [merge(I1, N1, L1, N2, L2) | sync2(T1, T2)]
    end.

%% Private function
-spec merge(id(), counter(), values(), counter(), values()) -> {id(), counter(), values()}.
merge(I, N1, L1, N2, L2) ->
    LL1 = length(L1),
    LL2 = length(L2),
    case N1 >= N2 of
        true ->
          case N1 - LL1 >=  N2 - LL2 of 
            true  -> {I, N1, L1};
            false -> {I, N1, lists:sublist(L1, N1 - N2 + LL2)}
          end;
        false ->
          case N2 - LL2 >=  N1 - LL1 of 
            true  -> {I, N2, L2};
            false -> {I, N2, lists:sublist(L2, N2 - N1 + LL1)}
          end
    end.


%% @doc Return a version vector that represents the causal history.
-spec join(clock()) -> vector().
join({C,_}) -> [{I, N} || {I, N, _} <- C].

%% @doc Advances the causal history with the given id.
%% The new value is the *anonymous dot* of the clock.
%% The client clock SHOULD BE a direct result of new/2.
-spec update(clock(), id()) -> clock().
update({C,[V]}, I) -> {event(C, I, V), []}.

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
update({Cc,[V]}, Cr, I) -> 
    %% Sync both clocks without the new value
    {C,Vs} = sync({Cc,[]}, Cr),
    %% We create a new event on the synced causal history,
    %% with the id I and the new value.
    %% The anonymous values that were synced still remain.
    {event(C, I, V), Vs}.

%% Private function
-spec event(vector(), id(), value()) -> vector().
event([], I, V) -> [{I, 1, [V]}];
event([{I, N, L} | T], I, V) -> [{I, N+1, [V | L]} | T];
event([{I1, _, _} | _]=C, I, V) when I1 > I -> [{I, 1, [V]} | C];
event([H | T], I, V) -> [H | event(T, I, V)].

%% @doc Returns the total number of values in this clock set.
-spec size(clock()) -> non_neg_integer().
size({C,Vs}) -> lists:sum([length(L) || {_,_,L} <- C]) + length(Vs).

%% @doc Returns all the ids used in this clock set.
-spec ids(clock()) -> [id()].
ids({C,_}) -> ([I || {I,_,_} <- C]).

%% @doc Returns all the values used in this clock set,
%% including the anonymous values.
-spec values(clock()) -> [value()].
values({C,Vs}) -> Vs ++ lists:append([L || {_,_,L} <- C]).

%% @doc Compares the equality of both clocks, regarding
%% only the causal histories, thus ignoring the values.
-spec equal(clock(), clock()) -> boolean().
equal({C1,_},{C2,_}) -> equal2(C1,C2).

%% Private function
-spec equal2(vector(), vector()) -> boolean().
equal2([], []) -> true;
equal2([{I, C, L1} | T1], [{I, C, L2} | T2]) when length(L1) == length(L2) -> equal(T1, T2);
equal2(_, _) -> false.

%% @doc Returns True if the first clock is causally older than
%% the second clock, thus values on the first clock are outdated.
%% Returns False otherwise.
-spec less(clock(), clock()) -> boolean().
less({C1,_}, {C2,_}) -> greater(C2, C1, false).

%% Private function
-spec greater(vector(), vector(), boolean()) -> boolean().
greater([], [], Strict) -> Strict;
greater([_|_], [], _) -> true;
greater([], [_|_], _) -> false;
greater([{I, N1, _} | T1], [{I, N2, _} | T2], Strict) ->
   if
     N1 == N2 -> greater(T1, T2, Strict);
     N1 >  N2 -> greater(T1, T2, true);
     N1 <  N2 -> false
   end;
greater([{I1, _, _} | T1], [{I2, _, _} | _]=C2, _) when I1 < I2 -> greater(T1, C2, true);
greater(_, _, _) -> false.

%% @doc Maps (applies) a function on all values in this clock set,
%% returning the same clock set with the updated values.
-spec map(fun((value()) -> value()), clock()) -> clock().
map(F, {C,Vs}) -> 
    {[ {I, N, lists:map(F, V)} || {I, N, V} <- C], lists:map(F, Vs)}.

%% @doc Returns the latest value in the clock set,
%% according to function F, which returns True if the 1st
%% value in "newer" than the 2nd value. False otherwise.
-spec last(After::fun((value(),value()) -> boolean()), clock()) -> value().
last(F, C) ->
   {_ ,_ , V2} = find_entry(F, C),
   V2.

%% @doc Return a clock with the same causal history, but with only one
%% value in the anonymous placeholder. This value is the latest value
%% in the given clock, according to the function F, which returns True
%% if the 1st value in "newer" than the 2nd value. False otherwise.
-spec lww(After::fun((value(),value()) -> boolean()), clock()) -> clock().
lww(F, C) ->
    case find_entry(F, C) of
        {id, I, V}      -> {join_and_replace(I, V, C),[]};
        {anonym, _, V}  -> {join(C),[V]}
    end.

%% find_entry/2 - Private function
find_entry(F, {[], [V|T]}) -> find_entry(F, null, V, {[],T}, anonym);
find_entry(F, {[{_, _, []} | T], Vs}) -> find_entry(F, {T,Vs});
find_entry(F, {[{I, _, [V|_]} | T], Vs}) -> find_entry(F, I, V, {T,Vs}, id).
%% find_entry/4 - Private function
find_entry(F, I, V, C, Flag) -> 
    Fun = fun (A,B) -> 
        case F(A,B) of 
            true  -> {left,A};
            false -> {right,B}
        end 
    end,
    find_entry2(Fun, I, V, C, Flag).
%% find_entry2/5 - Private function
find_entry2(_, I, V, {[], []}, anonym) -> {anonym, I , V};
find_entry2(_, I, V, {[], []}, id) -> {id, I, V};
find_entry2(F, I, V, {[], [V1 | T]}, Flag) ->
    case F(V, V1) of
        {left,V2}  -> find_entry2(F, I, V2, {[],T}, Flag);
        {right,V2} -> find_entry2(F, I, V2, {[],T}, anonym)
    end;
find_entry2(F, I, V, {[{_, _, []} | T], Vs}, Flag) -> find_entry2(F, I, V, {T, Vs}, Flag);
find_entry2(F, I, V, {[{I1, _, [V1|_]} | T], Vs}, Flag) -> 
    case F(V, V1) of
        {left,V2}  -> find_entry2(F, I, V2, {T, Vs}, Flag);
        {right,V2} -> find_entry2(F, I1, V2, {T, Vs}, Flag)
    end.

%% Private function
join_and_replace(Ir, V, C) -> 
    [if
       I == Ir -> {I, N, [V]};
       true    -> {I, N, []}
     end
     || {I, N, _} <- C].


%% ===================================================================
%% EUnit tests
%% ===================================================================
-ifdef(TEST).

update_test() ->
    A = new(a,v1),
    A1 = update(A,A,a,v2),
    ?assertEqual([{a,2,[v2]}], A1),
    A2 = update(A1,b,v3),
    ?assertEqual([{a,2,[]}, {b,1,[v3]}], A2),
    A2b = update(A1,A2,c,v3),
    A3 = update(A2b,a,v4),
    ?assertEqual([{a,3,[v4]}, {b,1,[]}, {c,1,[]}], A3),
    ok.

join_test() ->
    A = new(a,v),
    ?assertEqual(join(A), [{a,1,[]}]),
    B = new(b,v),
    C = update(B, B, b, v1),
    ?assertEqual(join(C), [{b,2,[]}]),
    D = sync(A, C),
    ?assertEqual(join(D), [{a,1,[]}, {b,2,[]}]),
    ok.

event_test() ->
    A = new(a,v1),
    ?assertEqual(event(A,a,v2), [{a,2,[v2,v1]}]),
    ?assertEqual(event(A,b,v2), [{a,1,[v1]}, {b,1,[v2]}]),
    ok.

sync_test() ->
    X = [{x,1,[]}],
    A = new(a,v1),
    Y = new(b,v2),
    A1 = update(A,a,v2),
    R1 = sync(A,A1),
    R2 = sync(A1,A),
    ?assertEqual(R1,R2),
    A2a = update(A1,b,v3),
    A2b = update(A1,c,v3),
    R3 = sync(A2b,A2a),
    ?assertEqual(R3, [{a,2,[]}, {b,1,[v3]}, {c,1,[v3]}]),
    ?assertEqual(R3, sync([A2b,A2a])),
    ?assertEqual(sync(X,A), [{a,1,[v1]},{x,1,[]}]), %% first clock MUST have a value!
    ?assertEqual(sync(X,A), sync(A,X)),
    ?assertEqual(sync(X,A), sync([A,X])),
    %% order by id when length of values is the same
    ?assertEqual(sync(A,Y), [{a,1,[v1]},{b,1,[v2]}]),
    ?assertEqual(sync(Y,A), sync(A,Y)), 
    ?assertEqual(sync(Y,A), sync([A,Y])), 
    ?assertEqual(sync(A,X), sync([X,A])),
    ok.

%lww_test() ->
%    ?assertEqual(v5, last([{a,1,[v0,v5]},{b,1,[]},{c,1,[v7]}])),
%    ?assertEqual([{a,2,[v5]},{b,1,[]},{c,2,[]}], lww([{a,1,[v0,v5]},{b,1,[]},{c,1,[v7]}])),
%    ok.

size_test() ->
    ?assertEqual(3, ?MODULE:size([{a,4,[v0,v5]},{b,0,[]},{c,1,[v3]}])),
    ok.

strict_descendant_test() ->
    A = new(a,v1),
    B = update(A,a,v2),
    B2 = update(A,b,v2),
    B3 = update(A,z,v2),
    C = update(B,A,c,v3),
    D = update(C,B2,d,v5),
    ?assert(strict_descendant(B,A)),
    ?assert(strict_descendant(C,A)),
    ?assert(strict_descendant(C,B)),
    ?assert(strict_descendant(D,B)),
    ?assert(strict_descendant(D,B2)),
    ?assert(strict_descendant(D,A)),
    ?assertNot(strict_descendant(C,B2)),
    ?assertNot(strict_descendant(B2,B)),
    ?assertNot(strict_descendant(B,B2)),
    ?assertNot(strict_descendant(A,A)),
    ?assertNot(strict_descendant(C,C)),
    ?assertNot(strict_descendant(B2,D)),
    ?assertNot(strict_descendant(D,B3)),
    ok.

equal_test() ->
    A = [{a,4,[v0,v5]},{b,0,[]},{c,1,[v3]}],
    B = [{a,4,[v0,v555]}, {b,0,[]}, {c,1,[v3]}],
    C = [{a,4,[v0,v5]},{b,0,[]}],
    % ignore the values' contents
    ?assert(equal(A,B)),
    ?assert(equal(B,A)),
    ?assertNot(equal(A,C)),
    ?assertNot(equal(B,C)),
    ok.

get_set_test() ->
    A = [{a,4,[v0,v5]},{b,0,[]},{c,1,[v3]}],
%    ?assertEqual(get_last(A), {a,4,[v0,v5]}),
%    ?assertEqual(last(A), v5),
    ?assertEqual(values(A), [v0,v5,v3]),
%    ?assertEqual(set_value(A,v9), [{a,4,[v9]},{b,0,[]},{c,1,[]}]),
%    ?assertEqual(set_value([{null,1,[v1]}],v9), [{null,1,[v9]}]),
    ok.

map_test() ->
    A = [{a,4,[5,0]},{b,0,[]},{c,1,[2]}],
    ?assertEqual(map(fun (X) -> X*X end,A), [{a,4,[25,0]},{b,0,[]},{c,1,[4]}]),
    ok.

-endif.
