% TODO:
% return {badarg,-1} in case of list processing
% clean code , unused comments
% ?) use try for more stability
% ?)more carefully and user frendly hadle local functions calls too
% 2)Handle enviroment variables by reading it from default config file or something else or and
% ?) admin mode without restriction for calls
% ?) sign foring modules and examine it before calls by tag -erls_sign(sign)
% ?) authorization
% ?) different roles for running code
% ?) test_and_log mode

-module(erls).
-description("Erlang methainterpretator (C) 2012, Dmitry Podkorytov").
-author("Dmitry Podkorytov").

-export([file/1,exec/1,inform_deny/1,test_l/0,test_p/0,test_d/0,scan/1,trace/1,trace/2,parse/1]).
-export([tests/0,test_t/0]).
-export([term_to_str/1,parse/1]).

trace(Term)->io:format("~p=~p~n",[scan(Term),Term]).

trace(FD,Term)->io:format(FD,"~p=~p~n",[scan(Term),Term]).

% transform program before scaning 
filter_scans(A)->A.

% it replace any denied call to call erls:inform_deny(Arg).
% list of allowed call is static yet in function permit({M,F,Arg})
% all locals calls in style of now() , without module name also locked (is it need) 

%%% transform program before parsing according to permit rules for mod & funcs.

%filter_parsing(A)->io:format("filter_parsing A=~p ~n",[A]),A.


filter_parsing({ok,List},allow_all)->{ok,List};
filter_parsing({ok,List},log_all)->io:format("filter_parsing: ~p~n",[{ok,List}]),{ok,List};

filter_parsing({ok,List},_)->{ok, filter_parsed_list(List)};
filter_parsing(T,_) when is_tuple(T)->
%io:format("filter_parsing T=~p ~n",[T]),
T.

filter_parsed_list([H])  -> [filter_parsed_node(H)]; % []->{dot,1};
filter_parsed_list([H|T])->[filter_parsed_node(H)|filter_parsed_list(T)].

filter_parsed_node({call,1,{remote,1,{atom,1,M},{atom,1,F}},Arg})->  
%case permit({M,F,Arg}) of
case permit_l({M,F,Arg}, [ {string,1,"A=~p ~n"},
                           {cons,1,{var,1,'A'},{nil,1}},
                           {io,format,Arg} ,
                           {erlang,now,Arg} ]
             ) of
 true-> {call,1,{remote,1,{atom,1,M},{atom,1,F}},Arg};
 _   -> {call,1,{remote,1,{atom,1,erls},{atom,1,inform_deny}},[{M,F,Arg}]}
end;

filter_parsed_node(Denied)->io:format("==--> local calls is anyway denied, need module name for call ~p ~n",[Denied]),
 {call,1,{remote,1,{atom,1,erls},{atom,1,inform_deny}},[Denied]}.

exec(Cmd) ->
    Scaned=filter_scans(scan(Cmd)),
    io:format("~p:~p Scaned=~p ~n",[?MODULE,?LINE,Scaned]),
    Parsed=filter_parsing(parse(Scaned),log_all),
    io:format("~p:~p Parsed=~p ~n",[?MODULE,?LINE,Parsed]),
    case eval(Parsed) of
        {error, _} -> {error,Cmd}; %% This should be an external call
        Term -> Term
    end.

file(Name)->
 {ok,Txt} = file:read_file(Name),
 exec(unicode:characters_to_list(Txt)).

scan(Cmd) -> erl_scan:string(Cmd).

parse({ok, Tokens, _}) -> erl_parse:parse_exprs(Tokens);
parse(Error) -> Error.

%%%%%%%%%% eval lists

eval(Expr_List)->
% trace(Expr_List),
 eval(Expr_List,erl_eval:new_bindings()).

eval({ok, Expr_list},Bindings) when is_tuple(Bindings)->
%    trace(Expr_list),
%   trace(Bindings),
    case (catch erl_eval:exprs(Expr_list,
                               erl_eval:new_bindings() 
                               %Bindings
                              )
         ) of
        {value, Value, _NewBindings} -> Value;
        {'EXIT', {Error, _}} -> {Error, -1};
        Error -> {Error, -1}
    end;

eval({ok,Expr},Bindings) 
 when is_list(Bindings) -> eval({ok,Expr},exec(Bindings));

eval(Error,Bindings) -> {eval_error,{Error, -1},Bindings}.

% depricated
make_node_call({M,F,Arg})->{call,1,{remote,1,{atom,1,M},{atom,1,F}},Arg}.

% handler for list of allowed functions and modules and arguments
%
% {module,function,arguments} -> true;
% {Module,Function,Arguments} -> true;
% ....
%
%List for allowed modules and functions 

permit([])->true;
permit([H|T])-> permit(H) and permit(T);
permit(MFARG)-> 
% turn on in test_and_log mode
io:format("==--> see permission for ~p ~n",[MFARG]),
%%%% need control for Arg
 case MFARG of
% {erlang,time,_}             ->false;
  {string,1,"A=~p ~n"}        ->true;
  {cons,1,{var,1,'A'},{nil,1}}->true;
  {io,_,Arg}     -> permit(Arg); % Arg;
  {erlang,now,_} -> true; % depricated make_node_call({erlang,now,A}); 
  A -> io:format("==--> deny for call ~p ~n",[A]), 
       false
 end.

permit_l(_,[])->false;
permit_l([],_)->true;
permit_l([H|T],L)-> permit_l(H,L) and permit_l(T,L);
permit_l(MFARG,[HL|TL])-> 
% turn on in test_and_log mode
io:format("==--> see permission for ~p ~n",[MFARG]),
%%%% need control for Arg
 case MFARG of

% {erlang,time,_} ->false;
%  HL             ->true;
%  {cons,1,{var,1,'A'},{nil,1}}->true;

  {_,_,Arg} -> permit_l(Arg,[HL|TL]); 
         HL -> true; 
          A -> io:format("==--> deny for call ~p ~n",[A]), false
 end 
 or permit_l(MFARG,TL).

%inform_deny(MFARG)-> io:format("==-->call is locked for ~p ~n",[erlang:term_to_binary(MFARG)]).
inform_deny(Term)-> io:format("==-->call is locked for term ~p ~n",[Term]).

term_to_str(Term) when is_integer(Term)->erlang:integer_to_list(Term);
term_to_str(Term) when is_list(Term)->Term;
term_to_str(Term) when is_atom(Term)->
SizeA=8*(erlang:size(erlang:term_to_binary(Term))-4),
case erlang:term_to_binary(Term) of
<<131,100,_,_,Atom:SizeA>>->erlang:bitstring_to_list(<<Atom:SizeA>>)
end;
term_to_str(Term) when is_function(Term)->
SizeA=8*(erlang:size(erlang:term_to_binary(Term))-7),
case erlang:term_to_binary(Term) of
<<131,112,_,_,_,_,_,F:SizeA>>->erlang:bitstring_to_list(<<F:SizeA>>)
end.

%%%% TESTS

test_ls()->erls:exec("[now(),now()].").
test_ls2()->erls:exec(" now(),now().").

test_p()->erls:exec("erlang:now().").
test_d()->erls:exec("erlang:time().").
test_t()->erls:exec("io:format(\"time: ~p ~n\",[[erlang:time(),erlang:time()]]).").

test_l()->erls:exec("now().").

test_v()->erls:exec(" A=erlang:now(),io:format(\"A=~p ~n\",[A]). ").

tests()->
[
test_d(),
test_l(),
test_ls(),
test_ls2(),
test_t(),
test_p(),
test_v()
].
 