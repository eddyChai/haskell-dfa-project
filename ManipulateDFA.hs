module ManipulateDFA 
where

import DFA
import Data.Char (isDigit, isLower)
import Data.List (sort, nub, (\\), map, elemIndex, elem)

{------------------------------------------------------------------------
   COMP 30026 Models Of Computation Assignment 2
   Last Edited by Stewart Collins - 326206 - 14/10/16
   Added to skeleton code provided for assignment 2 
   to complete assignment questions
------------------------------------------------------------------------}

--  Keep lists sorted and without duplicates.

tidy :: Ord a => [a] -> [a]
tidy xs
  = nub (sort xs)


--  Calculate the set of reachable states in a given DFA.

reachable :: DFA -> [State]
reachable (states, alphabet, delta, start_state, accept_states)
  = new
    where
      (old, new) = until stable explore ([], [start_state])
      explore (old_reach, cur_reach) = (cur_reach, expand cur_reach)
      expand reach = tidy (reach ++ successors reach)
      successors reach = [y | ((x,_),y) <- delta, x `elem` reach]
      stable (xs, ys) = xs == ys
      
--------------------------------------------------------------------------      

-- Question 5

--  Calculate the set of generating states in a given DFA.

generating :: DFA -> [State]
generating dfa@(states, alphabet, delta, start_state, accept_states)
  = generatingStates
    where
       generatingStates = [x | (x,y) <- stateList, y]
       stateList = [(x, containsAcceptState (stateReachable dfa x) accept_states )| x<-states]

--  Calculates whether a list of states contains an accept state

containsAcceptState :: [State] -> [State] -> Bool
containsAcceptState reachableStates acceptStates
  = elem True [reachableState == acceptState | reachableState <- reachableStates , acceptState <- acceptStates]

-- Calculates the reachable states from a given starting state in a DFA

stateReachable :: DFA -> State -> [State]
stateReachable (states, alphabet, delta, original_start_state, accept_states) new_start_state
  = reachable (states, alphabet, delta, new_start_state, accept_states)
                       

--  Trim a DFA, that is, keep only reachable, generating states
--  (the start state should always be kept).  

trim :: DFA -> DFA
trim dfa
  = recursiveTrim dfa (statesToTrim dfa)

recursiveTrim :: DFA -> [State] -> DFA
recursiveTrim inputDfa [] = inputDfa
recursiveTrim inputDfa (x:xs) = recursiveTrim (trimState inputDfa x) xs

    
statesToTrim :: DFA -> [State]
statesToTrim dfa@(states, alphabet, delta, start_state, accept_states)
  = [x | x<- states , (x `elem` usefulStates) /= True, x /= start_state]
    where
      usefulStates = tidy [x|  x<-generatingStates, y<-reachableStates, x == y]
      generatingStates = generating dfa
      reachableStates = reachable dfa
      
trimState :: DFA -> State -> DFA
trimState (states, alphabet, delta, start_state, accept_states) stateToRemove
  = trimmedDFA
     where 
       trimmedDFA = (trimmedStates, alphabet, trimmedDelta, start_state, trimmedAcceptStates)
       trimmedStates = [x | x<-states, x /= stateToRemove]
       trimmedDelta = [transition | transition@((start,sym),end) <- delta, start /= stateToRemove, end /= stateToRemove]
       trimmedAcceptStates = [x | x<-accept_states, x /= stateToRemove]

-------------------------------------------------------------------------
-- Question 6
--  Complete a DFA, that is, make all transitions explict.  For a DFA,
--  the transition function is always understood to be total.

complete :: DFA -> DFA
complete dfa@(states, alphabet, delta, start_state, accept_states)
  | length delta == length expandedDelta    =  dfa
  | otherwise = completedDFA
    where
      completedDFA = addTransitionsToRejectState expandedDFA rejectState rejectState
      expandedDFA@(_,_,expandedDelta,_,_)  = addAllRejectTransitions dfaWithRejectState states rejectState
      rejectState = last newStates
      dfaWithRejectState@(newStates,_,_,_,_) = addRejectState dfa
      
      
addAllRejectTransitions :: DFA -> [State] -> State -> DFA
addAllRejectTransitions inputDfa [] _ = inputDfa
addAllRejectTransitions inputDfa (x:xs) rejectState = addAllRejectTransitions (addTransitionsToRejectState inputDfa x rejectState) xs rejectState


addRejectState :: DFA -> DFA
addRejectState dfa@(states, alphabet, delta, start_state, accept_states)
  = (states ++ rejectState, alphabet, delta, start_state, accept_states)
    where 
      rejectState = take 1 [x | x <- infiniteStateList, (x `elem` states) /= True]
      
infiniteStateList :: [State]
infiniteStateList = [1..]

addTransitionsToRejectState :: DFA -> State -> State -> DFA
addTransitionsToRejectState dfa@(states, alphabet, delta, start_state, accept_states) stateToAddTransitions rejectState
  = revisedDfa
    where 
      revisedDfa = (states, alphabet, revisedDelta, start_state, accept_states)
      revisedDelta = delta ++ newTransitions
      newTransitions = [((stateToAddTransitions, x),rejectState)|x<-missingSymbols]
      missingSymbols = [x | x<-alphabet, ((stateToAddTransitions, x) `elem` map fst delta) /= True]

-------------------------------------------------------------------------
-- Question 7
--  Systematically replace the names of states in a DFA with 1..n.

normalise :: DFA -> DFA
normalise dfa@(states, alphabet, delta, start_state, accept_states)
  | (convertStateToInteger nextStateIndex) > length states = dfa
  | otherwise                      = normalise (swapState dfa originalState nextStateIndex)
    where
      originalState
        | 0 `elem` states    = 0
        | otherwise = head (take 1 [x | x <- (infiniteStateListFromStart ((convertStateToInteger nextStateIndex)+1)), (x `elem` states)])
      nextStateIndex = head (take 1 [x | x <- infiniteStateList, (x `elem` states) /= True])
      
convertStateToInteger :: State -> Int
convertStateToInteger x = x

infiniteStateListFromStart :: Int -> [State]
infiniteStateListFromStart start = [(start+1)..]

swapState :: DFA -> State -> State -> DFA
swapState inputDfa@(states, alphabet, delta, start_state, accept_states) originalState newState
  = outputDfa
    where
      outputDfa = (replacedStates, alphabet, replacedDelta, replacedStartState, replacedAcceptStates)
      replacedStates = [x | x<- states, x /= originalState] ++ [newState]
      replacedStartState
        | start_state == originalState  = newState
        | otherwise = start_state
      replacedAcceptStates
        | originalState `elem` accept_states  = [x | x<- accept_states, x /= originalState] ++ [newState]
        | otherwise  = accept_states
      replacedDelta = [((if start == originalState then newState else start,symbol),if end == originalState then newState else end)|((start,symbol),end)<-delta]

convertIndexToState :: Int -> State
convertIndexToState x = x

-------------------------------------------------------------------------

--  To complete and then normalise a DFA:

full :: DFA -> DFA
full
  = normalise . complete


-- Question 8
--  For a given DFA d, generate a DFA d' so that the languages of d
--  and d' are complementary.

complement :: DFA -> DFA
complement inputDfa
  = complementDfa
    where
      complementDfa = (states, alphabet, delta, start_state, reverseAcceptStates accept_states states)
      (states, alphabet, delta, start_state, accept_states) = complete inputDfa
  
reverseAcceptStates :: [State] -> [State] -> [State]
reverseAcceptStates inputAcceptStates allStates
  = outputAcceptStates
     where
       outputAcceptStates = [x | x <- allStates , (x `elem` inputAcceptStates) /= True]

-------------------------------------------------------------------------

-- Question 9

type ProductState = (State, State)
type ProductTrans = ((ProductState,Sym), ProductState)
type ProductDFA = ([ProductState], [Sym],[ProductTrans], ProductState ,[ProductState])

--  Given DFAs d1 and d', generate a DFA for the intersection of the
--  languages recognised by d1 and d2.

prod :: DFA -> DFA -> DFA
prod dfa1 dfa2
  = normalise (trim (normaliseProductDFA (productDFA (complete (trim dfa1)) (complete (trim dfa2)))))


-- Normalises productDFA to DFA format by replacing ProductState references with normalised State

normaliseProductDFA :: ProductDFA -> DFA
normaliseProductDFA prodDfa@(combinedStates, alphabet, _, combinedStartState, combinedAcceptStates)
  = (normalisedStates, alphabet, normalisedDelta, normalisedStartState, normalisedAcceptStates)
    where 
      normalisedDelta = getNormalisedDelta prodDfa
      normalisedStartState = getNormalisedState combinedStartState combinedStates
      normalisedAcceptStates = [getNormalisedState x combinedStates|x<-combinedAcceptStates]
      normalisedStates = take (length combinedStates) infiniteStateList

-- Returns a [Trans] DFA equivalent of [ProductTrans] in ProductDFA with ProductStates replaced with States 
      
getNormalisedDelta :: ProductDFA -> [Trans]
getNormalisedDelta prodDfa@(combinedStates, alphabet, combinedDelta, combinedStartState, combinedAcceptStates)
  = [((getNormalisedState combinedStart combinedStates,symbol),getNormalisedState combinedEnd combinedStates)|((combinedStart,symbol),combinedEnd) <-combinedDelta]


-- Returns the normalised State of a ProductState, relies on the convention that states are renamed according to their position in combinedStates list

getNormalisedState :: ProductState -> [ProductState] -> State
getNormalisedState combinedState combinedStates
  = convertIndexToState (index+1)
    where
      index = convertMaybeInt (elemIndex combinedState combinedStates)

-- Given two DFAs as input construct a productDFA with the states named as combinations of original states

productDFA :: DFA -> DFA -> ProductDFA
productDFA dfa1@(states1, alphabet, delta1, start_state1, accept_states1) dfa2@(states2, _, delta2, start_state2, accept_states2)
  = (combinedStates, alphabet, combinedDelta, combinedStartState, combinedAcceptStates)
    where
      combinedDelta = deltaProduct dfa1 dfa2
      combinedStates = statesProduct states1 states2
      combinedAcceptStates = statesProduct accept_states1 accept_states2
      combinedStartState = stateProduct start_state1 start_state2

      
-- Returns a product state from two given states
      
stateProduct :: State -> State -> ProductState
stateProduct state1 state2 = (state1,state2)


-- Creates a list of all possible states in the product of two dfas

statesProduct :: [State] -> [State] -> [ProductState]
statesProduct dfa1States dfa2States
 = [(x,y)|x<-dfa1States,y<-dfa2States]

 
-- Creates a list of all possible transitions from all possible state combinations in the two dfas (note could be much more efficient by exploring reachable 
-- nodes rather than generating all possible transitions for states that may not be reachable, but should still produce correct result)
 
deltaProduct :: DFA -> DFA -> [ProductTrans]
deltaProduct dfa1@(states1,_,delta1,_,_) dfa2@(states2,_,delta2,_,_)
  = concat transitionProduct
    where 
      transitionProduct = [newTransitions (x,y) (stateTransitions delta1 x) (stateTransitions delta2 y) | x<-states1, y<-states2]

      
-- Creates a list of all possible product transitions in both deltas from a given product start state
      
newTransitions :: ProductState -> [Trans] -> [Trans] -> [ProductTrans]
newTransitions startState delta1 delta2
 = [((startState,symbol1),(state3,state4))|((_,symbol1),state3)<-delta1,((_,symbol2),state4)<-delta2, symbol1 == symbol2]

 
-- Returns all the transitions in delta from a given starting state

stateTransitions :: [Trans] -> State -> [Trans]
stateTransitions delta state= [((x,y),z)|((x,y),z)<-delta,x == state]

-- Converts a maybe int to and int, returns -1 if maybe int == nothing
  
convertMaybeInt :: Maybe Int -> Int
convertMaybeInt maybeInt
  = maybe (-1) intToInt maybeInt

  
-- Helper function used by maybe to return an int
  
intToInt :: Int -> Int
intToInt n = n

-------------------------------------------------------------------------

--  Here is an example (trimmed) DFA; it recognises a*ab*c*

dex :: DFA 
dex 
  = ([0,1,2,3], "abc", t1, 0, [1,2,3])
    where 
      t1 = [ ((0,'a'), 1)
           , ((1,'a'), 1)
           , ((1,'b'), 2)
           , ((1,'c'), 3)
           , ((2,'b'), 2)
           , ((2,'c'), 3)
           , ((3,'c'), 3)
           ]

-------------------------------------------------------------------------
-- Test DFAs used

dfa1 :: DFA 
dfa1 
  = ([0,5,3,6], "abc", t1, 0, [5])
    where 
      t1 = [ ((0,'a'), 5)
           , ((0,'b'), 6)
           , ((0,'c'), 6)
           , ((5,'a'), 6)
           , ((5,'b'), 5)
           , ((5,'c'), 6)
           , ((6,'a'), 6)
           , ((6,'b'), 6)
           , ((6,'c'), 6)
           , ((3,'a'), 0)
           , ((3,'b'), 3)
           , ((3,'c'), 6)
           ]
           
dfa2 :: DFA 
dfa2 
  = ([1,2], "ab", t1, 1, [1])
    where 
      t1 = [ ((1,'a'), 2)
           , ((1,'b'), 1)
           , ((2,'a'), 1)
           , ((2,'b'), 2)
           ]
           
dfa3 :: DFA 
dfa3 
  = ([3,4], "ab", t1, 3, [4])
    where 
      t1 = [ ((3,'a'), 3)
           , ((3,'b'), 4)
           , ((4,'a'), 4)
           , ((4,'b'), 3)
           ]