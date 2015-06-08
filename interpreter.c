// interpreter.c 

// Created by Jerry Zhou and Cody Bohlman
// This first part of the actual interpreting - Currently only works with 
// Racket code, using only the if and let functions. 

// Include statements
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "tokenizer.h"
#include "value.h"
#include "linkedlist.h"
#include "parser.h"
#include "talloc.h"
#include "interpreter.h"

// Declaration of methods that are not in the header file interpreter.h
void printValue(Value* value);
Value* lookUpSymbol(Value* tree, Frame* frame);
Value* findPair(Value* tree, Frame* frame);
void evaluationError();
void printTree_2(Value* value);
Value* evalBegin(Value* args, Frame* frame);
Value* evalIf(Value* args, Frame* frame);
Value* evalCond(Value* args, Frame* frame);
Value* evalLet(Value* args, Frame* frame);
Value* evalLetRec(Value* args, Frame* frame);
Value* evalLetStar(Value* args, Frame* frame);
Value* evalSetBang(Value* args, Frame* frame);
Value* apply(Value *function, Value *args);
Value* evalQuote(Value* args,Frame* frame);
Value* evalLambda(Value* args, Frame* frame);
Value* evalDefine(Value* args, Frame* frame);
Value* evalEach(Value* args,Frame* frame);


// Evaluates an 'if' statement, and does error checking to make sure
// the input is valid
Value* evalIf(Value* args, Frame* frame) {
    //Checks if there are 3 things in args 
    int count = 0;
    Value* current = args;
    while (current->type != NULL_TYPE){
        count +=1;
        current = cdr(current);
    }
    if(count!=3){
        //printf("If - arguments > 3\n");
        evaluationError();
    }
    
    //Checks if the first thing in args is a BOOL_TYPE
    
    Value* first = eval(eval(car(args),frame),frame);
    
    //printValue(first);printf("\n");
    if ( first->type != BOOL_TYPE ){
        //printf("evalIf - first args not BOOL_TYPE\n");
        evaluationError();
    }
    //Evaluating "if"
    if (first->i == 1){
        //printf("If -Evaluating true\n");
        return eval( car(cdr(args)), frame);
    } else {
        //printf("If -Evaluating false\n");
        return eval( car(cdr(cdr(args))),frame );
    }

}

// Evaluates the 'cond' function in racket. Evaluates left to right: if it finds a true, evaluates
// whatever follows. If no true if found, and an else is found at the rightmost location, evaluates whatever
// 
Value* evalCond(Value* args, Frame* frame){
    Value* current = args;
    while (current->type != NULL_TYPE){
        if(current->type == CONS_TYPE ){
            Value* first = car(car(current));
            if (first->type == SYMBOL_TYPE){
                if(!strcmp(first->s, "else")){
                    if(cdr(current)->type == NULL_TYPE) {
                        return evalBegin(cdr(car(current)), frame);
                    }
                    else {
                        //printf(" Error - evalCond: else is not last\n");
                        evaluationError();
                    }
                }
                else if(lookUpSymbol(first,frame)->type == BOOL_TYPE){
                    if(lookUpSymbol(first,frame)->i == 1) {
                        return evalBegin(cdr(car(current)), frame);
                    }
                }else{
                    evaluationError();
                } 
            }
            
           
            else if (first->type == BOOL_TYPE || first->type == CONS_TYPE ){
                first = eval(car(car(current)),frame);
                if (first->i == 1){
                    return evalBegin(cdr(car(current)),frame);
                }
            }
            else{
                //printf(" Error - evalCond: first thing is not a boolean or else\n");
                evaluationError();
            }
        }
        current = cdr(current);
    }
    Value* voidtype = makeNull();
    voidtype->type = VOID_TYPE;
    return voidtype;
    
}


// A helper function that creates a new frame, given a list of bindings and a 
// parent frame. Also does error checking
Frame* newFrame(Value* pairs, Frame* frame){

    //Creates new frame "on top" of old frame.
    Frame* new_frame =  talloc(sizeof(Frame));
    new_frame->bindings = makeNull();
    new_frame->parent = frame;
    
    //Checks if the pairs given is correct format. 
    //The pairs should be a list of 2-item lists, with the car of each sublist being a SYMBOL_TYPE.
    
    Value* current = pairs;
    while (current->type != NULL_TYPE){
        Value* pair = car(current);
        if(pair->type != CONS_TYPE){
            //printf("Frame-Bindings not a list of pairs\n");
            evaluationError();
        }
        if(car(pair)->type != SYMBOL_TYPE ){
            //printf("Frame- First thing in pair is not a symbol\n");
            evaluationError();
        }
        if (length(pair) !=  2){
            //printf("Frame- Things in list are not pairs l\n");
            evaluationError();
        }
        if(cdr(pair)->type == CONS_TYPE) {
            Value* second = eval(car(cdr(pair)),frame);
            Value* new_binding = makeNull();
            new_binding = cons(second,new_binding);
            new_binding = cons(car(pair), new_binding);
            new_frame->bindings = cons(new_binding,new_frame->bindings);
            current = cdr(current); 
        }
        else {
            //printf("Not a cons type.. aborting\n");   
            evaluationError();
        }
    }   
    return new_frame;
}

// This function evaluates a 'let' function as defined by the Racket 'let' 
// function, and returns a Value*. Does error checking
Value* evalLet(Value* args,Frame* frame){
    //Checks if there are 2 things in args 
    int count = 0;
    Value* current = args;
    while (current->type != NULL_TYPE){
        count +=1;
        current = cdr(current);
    }
    
    if(count!=2){
        //printf("Let-there are not 2 arguments\n");
        evaluationError();
    }
    
    //Create new frame with first arg and evaluate second arg
    Frame* newframe = newFrame( car(args), frame );
    return eval( car(cdr(args)),newframe );
}

// Evaluates the 'let*' function in racket. Evaluates/binds parameters left to right
Value* evalLetStar(Value* args, Frame* frame){
    if (length(args)!= 2){
        //printf("Let-there are not 2 arguments\n");
        evaluationError();
    }
   
    Value* pairs = car(args);
    Value* current = pairs;
    while (current->type != NULL_TYPE){
        Value* pair = car(current);
        if(pair->type != CONS_TYPE){
            //printf("Frame-Bindings not a list of pairs\n");
            evaluationError();
        }
        if(car(pair)->type != SYMBOL_TYPE ){
            //printf("Frame- First thing in pair is not a symbol\n");
            evaluationError();
        }
        if (length(pair) !=  2){
            //printf("Frame- Things in list are not pairs l\n");
            evaluationError();
        }
        if(cdr(pair)->type == CONS_TYPE) {
            Frame* new_frame =  talloc(sizeof(Frame));
            new_frame->bindings = makeNull();
            new_frame->parent = frame;
            
            Value* second = eval(car(cdr(pair)),frame);
            Value* new_binding = makeNull();
            new_binding = cons(second,new_binding);
            new_binding = cons(car(pair), new_binding);
            new_frame->bindings = cons(new_binding,new_frame->bindings);
            
            frame = new_frame;
            current = cdr(current); 
        }
        else {
            //printf("Not a cons type.. aborting\n");   
            evaluationError();
        }
    }   
    return eval( car(cdr(args)),frame );
    
}

// Evaluates the 'letrec' function in racket. Evaluates the parameters left to right, and makes parameters
// available as soon as they are binded.
Value* evalLetRec(Value* args, Frame* frame){
    if (length(args)!= 2){
        //printf("Let-there are not 2 arguments\n");
        evaluationError();
    }
   
    Frame* new_frame =  talloc(sizeof(Frame));
    new_frame->bindings = makeNull();
    new_frame->parent = frame;
    
    Value* pairs = car(args);
    Value* current = pairs;
    while (current->type != NULL_TYPE){
        Value* pair = car(current);
        if(pair->type != CONS_TYPE){
            //printf("Frame-Bindings not a list of pairs\n");
            evaluationError();
        }
        if(car(pair)->type != SYMBOL_TYPE ){
            //printf("Frame- First thing in pair is not a symbol\n");
            evaluationError();
        }
        if (length(pair) !=  2){
            //printf("Frame- Things in list are not pairs l\n");
            evaluationError();
        }
        if(cdr(pair)->type == CONS_TYPE) {
            Value* second = eval(car(cdr(pair)),new_frame);
            Value* new_binding = makeNull();
            new_binding = cons(second,new_binding);
            new_binding = cons(car(pair), new_binding);
            new_frame->bindings = cons(new_binding,new_frame->bindings);
            current = cdr(current); 
        }
        else {
            //printf("Not a cons type.. aborting\n");   
            evaluationError();
        }
    }   
    return eval( car(cdr(args)),new_frame );
    
}

// Evaluates the 'set!' function in racket. Reassigns the parameter to the given value.
Value* evalSetBang(Value* args, Frame* frame){
    int count = 0;
    Value* current = args;
    while (current->type != NULL_TYPE){
        count +=1;
        current = cdr(current);
    }
    if (car(args)->type != SYMBOL_TYPE){
        //printf("Error -define params are not all symbols\n");
        evaluationError();
    }
    if(count == 2){
        Value* set = talloc(sizeof(Value));
        set->type = VOID_TYPE;
        Value* second = eval(car(cdr(args)),frame);
        
        Value* pair = findPair(car(args),frame);
        Value* cdr = pair->c.cdr;
        cdr->c.car = second;
        
        return set;
    }else{
        //printf("Error -define does not have 2 arguments\n");
        evaluationError();
        return args;
    }
    
}

// Evaluates the 'begin' function in racket. Evaluates each of its arguments,
// and returns the result of the last argument
Value* evalBegin(Value* args, Frame* frame) {
    // The length can be anything greater than or equal to zero, so no error checking needed for that
    
    Value* current = evalEach(args,frame);
    //printValue(args);printf("\n");
    while(current->type != NULL_TYPE) {
        if(current->type == CONS_TYPE) {
            if(cdr(current)->type == NULL_TYPE) {
                //printf("Got here\n");
                return car(current);   
            }
        }
        current = cdr(current);
    }
    // Something went wrong.
    Value* voidtype = makeNull();
    voidtype->type = VOID_TYPE;
    return voidtype;
}

// Evaluates the quote operator
Value* evalQuote(Value* tree, Frame* frame){
    int count = 0;
    Value* current = tree;
    while (current->type != NULL_TYPE){
        count +=1;
        current = cdr(current);
    }
    if(count == 1){
        return car(tree);
    }else{
        //printf("Error in quote\n");
        evaluationError();
        return tree;
    }
}

// Creates a closure type, with a pointer to its frame, the param names, and 
// the function code, as defined in the racket code.
Value* evalLambda(Value* args, Frame* frame){
    int count = 0;
    Value* current = args;
    while (current->type != NULL_TYPE){
        count +=1;
        current = cdr(current);
    }
    Value* params = car(args);
    while (params->type != NULL_TYPE){
        if (params->type != CONS_TYPE){
            //printf("Error -lambda params are not all CONS\n");
            evaluationError();
        }
        else {
            if (car(params)->type != SYMBOL_TYPE) {
                //printf("Error not a symbol\n");
                evaluationError();
            }
        }
        params = cdr(params);
    }
    if(count == 2){
        
        Value* closure = talloc(sizeof(Value));
        closure->type = CLOSURE_TYPE;
        closure->cl.frame = frame;
        closure->cl.paramNames = car(args);
        closure->cl.functionCode = car(cdr(args));
        return closure;
    }else{
        //printf("Error -lambda does not have 2 arguments\n");
        evaluationError();
        return args;
    }
    
}

// Evaluates the define operator, which will return a Value* of type void.
// Updates the frame so there is a new binding, appended onto the current list of
// bindings in the frame
Value* evalDefine(Value* args, Frame* frame){
    int count = 0;
    Value* current = args;
    while (current->type != NULL_TYPE){
        count +=1;
        current = cdr(current);
    }
    if (car(args)->type != SYMBOL_TYPE){
        //printf("Error -define params are not all symbols\n");
        evaluationError();
    }
    if(count == 2){
        Value* define = talloc(sizeof(Value));
        define->type = VOID_TYPE;
        Value* second = eval(car(cdr(args)),frame);
        Value* new_binding = makeNull();
        new_binding = cons(second,new_binding);
        new_binding = cons(car(args), new_binding);
        
        frame->bindings = cons(new_binding,frame->bindings);
        return define;
    }else{
        //printf("Error -define does not have 2 arguments\n");
        evaluationError();
        return args;
    }
    

}

// Evaluates each item in the linked list, and creates a new linked list 
// of these evaluated items. From here, we reverse the list (it is initially a "stack")
// and then return it
Value* evalEach(Value* args,Frame* frame){
    Value* list = makeNull();
    while (args->type != NULL_TYPE){
        if(args->type == CONS_TYPE) {
            Value* item = eval(car(args),frame);
            list = cons(item, list);
            args = cdr(args);
            if(args == NULL) {
                break;   
            }
        }
        else {
            //printf("NOT CONS IN EVAL EACH\n");
            Value* item = eval(args,frame);
            list = cons(item, list);
        }
        
    }
    return reverse(list);
    
}

// Applys the  given function to the arguments, and returns the
// evaluation
Value* apply(Value* function, Value* args){
    Frame* curr_frame = function->cl.frame;
    Value* pairs = makeNull();
    Value* params = function->cl.paramNames;
    if(function->type != CLOSURE_TYPE && function->type != PRIMITIVE_TYPE){
        //printf("Error -apply does not have a closure/function\n");
        evaluationError();
    }
    
    if (function->type == CLOSURE_TYPE){
        while(args->type != NULL_TYPE){
            if(params->type == NULL_TYPE){
                //printf("Error -number of args and number of params don't match\n");
                evaluationError();
            }

            Value* new_binding = makeNull();
            new_binding = cons(car(args), new_binding);
            new_binding = cons(car(params),new_binding);

            pairs = cons(new_binding,pairs);
            
            args = cdr(args);
            params = cdr(params);
        }
        if (args->type == NULL_TYPE && params->type == NULL_TYPE) {
            Frame* newframe = newFrame(pairs,curr_frame);
            return eval(function->cl.functionCode, newframe); 
        }else{
            //printf(" ELSE Error -number of args and number of params don't match\n");
            evaluationError();
            return function;
        }
    } else if (function->type == PRIMITIVE_TYPE){
        Frame* newframe = newFrame(pairs,curr_frame);
        Value* result = function->pf(args);
        return result;  
    }
    return args;
}

// This function returns the Value* assocated with a given symbol and frame. Will
// look to the parent frame if the symbol is not found within the current frame, and 
// does error checking.i
Value* lookUpSymbol(Value* tree, Frame* frame){
    char* string = tree->s;
    Value* binding_list = frame->bindings;
    if (frame->parent == NULL){
        //printf("LookupSymbol-Symbol not found:"); printValue(tree);printf("\n");
        evaluationError();
    }
    
    while(binding_list->type != NULL_TYPE) {
        Value* pair = car(binding_list);
        
        if(!strcmp(string, car(pair)->s)) {
            return car(cdr(pair));
        }
        binding_list = cdr(binding_list);
    }
    return lookUpSymbol(tree, frame->parent);
}

Value* findPair(Value* tree, Frame* frame){
    char* string = tree->s;
    Value* binding_list = frame->bindings;
    if (frame->parent == NULL){
        //printf("LookupSymbol-Symbol not found:"); printValue(tree);printf("\n");
        evaluationError();
    }
    
    while(binding_list->type != NULL_TYPE) {
        Value* pair = car(binding_list);
        
        if(!strcmp(string, car(pair)->s)) {
            return pair;
        }
        binding_list = cdr(binding_list);
    }
    return findPair(tree, frame->parent);
}


// This function executes if an error occurs in the interpreting, for any number of 
// reasons.
void evaluationError(){
    printf("evaluation error\n");
    texit(1);
}

// Evaluates the 'and' operator in racket. Returns true if all parameters are true, and false otherwise
Value* evalAnd(Value* args,Frame* frame) {
    if(length(args) < 2) {
        evaluationError();  
        return makeNull();
    }
    else {
        int boolean = 1;
        Value* current = evalEach(args,frame);
        if(current->type == CONS_TYPE) {
            while(current->type != NULL_TYPE) {
                if(car(current)->type == BOOL_TYPE) {
                    if(car(current)->i == 0) {
                        boolean = 0;   
                        //break;
                    }
                }
                else {
                    evaluationError();                                 
                }     
                current = cdr(current);
            }
        }
        else {
            evaluationError();   
        }
        Value* returnValue = makeNull();
        returnValue->type = BOOL_TYPE;
        returnValue->i = boolean;
        return returnValue;
    }
}

// Evaluates the 'or' function in racket. Returns true if one or more of the parameters are true, false otherwise
Value* evalOr(Value* args,Frame* frame) {
    if(length(args) < 2) {
        evaluationError();  
        return makeNull();
    }
    else {
        int boolean = 0;
        Value* current = evalEach(args,frame);
        if(current->type == CONS_TYPE) {
            while(current->type != NULL_TYPE) {
                if(car(current)->type == BOOL_TYPE) {
                    if(car(current)->i == 1) {
                        boolean = 1;   
                        //break;
                    }
                }
                else {
                    evaluationError();                                 
                }     
                current = cdr(current);
            }
        }
        else {
            evaluationError();   
        }
        Value* returnValue = makeNull();
        returnValue->type = BOOL_TYPE;
        returnValue->i = boolean;
        return returnValue;
    }
}

// Evaluates the '>=' function in racket. Returns true if the first argument is larger than or
// equal to the second argument (numerically), and returns false otherwise
Value* primitiveGreaterThanEqualTo(Value* args) {
    if(length(args) != 2) {
        evaluationError();
        return makeNull();
    }
    else {
        double num1 = 0;
        double num2;
        if(args->type == CONS_TYPE) {
            if(car(args)->type == INT_TYPE) {
                num1 = car(args)->i;
            }
            else if(car(args)->type == DOUBLE_TYPE) {
                num1 = car(args)->d;
            }
            else {
                evaluationError();   
            }
            num2 = 0;
            if(car(cdr(args))->type == INT_TYPE) {
                num2 = car(cdr(args))->i;
            }
            else if(car(cdr(args))->type == DOUBLE_TYPE) {
                num2 = car(cdr(args))->d;
            }
            else {
                evaluationError();   
            }
        }
        else {
            evaluationError();   
        }
        
        Value* returnValue = makeNull();
        returnValue->type = BOOL_TYPE;
        if(num1 >= num2) {
            returnValue->i = 1;   
        }
        else {
            returnValue->i = 0;  
        }
        return returnValue;
    }
}

// Evaluates the '<=' function in racket. Returns true if the first argument is smaller than or
// equal to the second argument (numerically), and returns false otherwise
Value* primitiveLessThanEqualTo(Value* args) {
    if(length(args) != 2) {
        evaluationError();
        return makeNull();
    }
    else {
        double num1 = 0;
        double num2;
        if(args->type == CONS_TYPE) {
            if(car(args)->type == INT_TYPE) {
                num1 = car(args)->i;
            }
            else if(car(args)->type == DOUBLE_TYPE) {
                num1 = car(args)->d;
            }
            else {
                evaluationError();   
            }
            num2 = 0;
            if(car(cdr(args))->type == INT_TYPE) {
                num2 = car(cdr(args))->i;
            }
            else if(car(cdr(args))->type == DOUBLE_TYPE) {
                num2 = car(cdr(args))->d;
            }
            else {
                evaluationError();   
            }
        }
        else {
            evaluationError();   
        }
        
        Value* returnValue = makeNull();
        returnValue->type = BOOL_TYPE;
        if(num1 <= num2) {
            returnValue->i = 1;   
        }
        else {
            returnValue->i = 0;  
        }
        return returnValue;
    }
}

// Evaluates the '=' function in racket. Returns true if the first argument is 
// equal to the second argument (numerically), and returns false otherwise
Value* primitiveEqualTo(Value* args) {
    if(length(args) != 2) {
        evaluationError();
        return makeNull();
    }
    else {
        double num1 = 0;
        double num2;
        if(args->type == CONS_TYPE) {
            if(car(args)->type == INT_TYPE) {
                num1 = car(args)->i;
            }
            else if(car(args)->type == DOUBLE_TYPE) {
                num1 = car(args)->d;
            }
            else {
                evaluationError();   
            }
            num2 = 0;
            if(car(cdr(args))->type == INT_TYPE) {
                num2 = car(cdr(args))->i;
            }
            else if(car(cdr(args))->type == DOUBLE_TYPE) {
                num2 = car(cdr(args))->d;
            }
            else {
                evaluationError();   
            }
        }
        else {
            evaluationError();   
        }
        
        Value* returnValue = makeNull();
        returnValue->type = BOOL_TYPE;
        if(num1 == num2) {
            returnValue->i = 1;   
        }
        else {
            returnValue->i = 0;  
        }
        return returnValue;
    }
}

// Evaluates the '<' function in racket. Returns true if the first argument is smaller than 
// the second argument (numerically), and returns false otherwise
Value* primitiveLessThan(Value* args) {
    if(length(args) != 2) {
        evaluationError();
        return makeNull();
    }
    else {
        double num1 = 0;
        double num2;
        if(args->type == CONS_TYPE) {
            if(car(args)->type == INT_TYPE) {
                num1 = car(args)->i;
            }
            else if(car(args)->type == DOUBLE_TYPE) {
                num1 = car(args)->d;
            }
            else {
                evaluationError();   
            }
            num2 = 0;
            if(car(cdr(args))->type == INT_TYPE) {
                num2 = car(cdr(args))->i;
            }
            else if(car(cdr(args))->type == DOUBLE_TYPE) {
                num2 = car(cdr(args))->d;
            }
            else {
                evaluationError();   
            }
        }
        else {
            evaluationError();   
        }
        
        Value* returnValue = makeNull();
        returnValue->type = BOOL_TYPE;
        if(num1 < num2) {
            returnValue->i = 1;   
        }
        else {
            returnValue->i = 0;  
        }
        return returnValue;
    }
}

// Evaluates the '>' function in racket. Returns true if the first argument is larger than 
// the second argument (numerically), and returns false otherwise
Value* primitiveGreaterThan(Value* args) {
    if(length(args) != 2) {
        evaluationError();
        return makeNull();
    }
    else {
        double num1 = 0;
        double num2;
        if(args->type == CONS_TYPE) {
            if(car(args)->type == INT_TYPE) {
                num1 = car(args)->i;
            }
            else if(car(args)->type == DOUBLE_TYPE) {
                num1 = car(args)->d;
            }
            else {
                evaluationError();   
            }
            num2 = 0;
            if(car(cdr(args))->type == INT_TYPE) {
                num2 = car(cdr(args))->i;
            }
            else if(car(cdr(args))->type == DOUBLE_TYPE) {
                num2 = car(cdr(args))->d;
            }
            else {
                evaluationError();   
            }
        }
        else {
            evaluationError();   
        }
        
        Value* returnValue = makeNull();
        returnValue->type = BOOL_TYPE;
        if(num1 > num2) {
            returnValue->i = 1;   
        }
        else {
            returnValue->i = 0;  
        }
        return returnValue;
    }
}

// Implements modulo in Racket, returning errors if there is bad input.
// Works with both INT_TYPE and DOUBLE_TYPE, but will always return a DOUBLE_TYPE Value*.
Value* primitiveModulo(Value* args) {
    if(length(args) != 2) {
        evaluationError();
        return makeNull();
    }
    else {
        int modulo = 0;
        int negative1 = 0;
        int negative2 = 0;
        if(args->type == CONS_TYPE) {
            if(car(args)->type == INT_TYPE) {
                int num1 = car(args)->i;
                int num2 = 0;
                if(num1 < 0) {
                    negative1 = 1;   
                }
                if(car(cdr(args))->type == INT_TYPE) {
                    num2 = car(cdr(args))->i;
                    if(num2 < 0) {
                        negative2 = 1;
                    }
                }
                else {
                    evaluationError();   
                }
                
                // Check to see which nums are negative
                if(negative1 == 1) {
                    if(negative2 == 1) {
                        modulo = 0 - div(num1, num2).rem;
                    }
                    else {
                        modulo = num2 - div(num1, num2).rem;
                    }
                }
                else {
                    if(negative2 == 1) {
                        modulo = 0 - (abs(num2) - div(num1, num2).rem);
                    }
                    else {
                        modulo = div(num1,num2).rem;
                    }
                }
            }
            else {
                evaluationError();
            }
        }
        else {
            //printf("Not a type\n");
            evaluationError();
        }
        Value* returnValue = makeNull();
        returnValue->type = INT_TYPE;
        returnValue->i = modulo;
        return returnValue;
    }
}

// Implements division in Racket, returning errors if there is bad input.
// Works with both INT_TYPE and DOUBLE_TYPE, but will always return a DOUBLE_TYPE Value*.
Value* primitiveDivide(Value* args) {
    if(length(args) != 2) {
        evaluationError();
        return makeNull();
    }
    else {
        double quotient = 0;
        if(args->type == CONS_TYPE) {
            if(car(args)->type == INT_TYPE) {
                double num1 = (double) car(args)->i;
                double num2 = 0.0;
                if(car(cdr(args))->type == INT_TYPE) {
                    num2 = car(cdr(args))->i;
                }
                else if(car(cdr(args))->type == DOUBLE_TYPE) {
                    num2 = car(cdr(args))->d;   
                }
                else {
                    evaluationError();   
                }
                quotient = num1 / num2;   
            }
            else if (car(args)->type == DOUBLE_TYPE) {
                double num1 = car(args)->d;
                double num2 = 0.0;
                if(car(cdr(args))->type == INT_TYPE) {
                    num2 = car(cdr(args))->i;
                }
                else if(car(cdr(args))->type == DOUBLE_TYPE) {
                    num2 = car(cdr(args))->d;   
                }
                else {
                    evaluationError();   
                }
                quotient = num1 / num2;  
            }
            else {
                evaluationError();
            }
        }
        else {
            //printf("Not a type\n");
            evaluationError();
        }
        Value* returnValue = makeNull();
        returnValue->type = DOUBLE_TYPE;
        returnValue->d = quotient;
        return returnValue;
    }
}

// Implements subtraction in Racket, returning errors if there is bad input.
// Works with both INT_TYPE and DOUBLE_TYPE, but will always return a DOUBLE_TYPE Value*.
Value *primitiveSubtract(Value* args) {
    if(length(args) != 2) {
        evaluationError();
        return makeNull();
    }
    else {
        double subtraction = 0;
        if(args->type == CONS_TYPE) {
            if(car(args)->type == INT_TYPE) {
                int num1 = car(args)->i;
                double num2 = 0.0;
                if(car(cdr(args))->type == INT_TYPE) {
                    num2 = car(cdr(args))->i;
                }
                else if(car(cdr(args))->type == DOUBLE_TYPE) {
                    num2 = car(cdr(args))->d;   
                }
                else {
                    evaluationError();   
                }
                subtraction = num1 - num2;   
            }
            else if (car(args)->type == DOUBLE_TYPE) {
                double num1 = car(args)->d;
                double num2 = 0.0;
                if(car(cdr(args))->type == INT_TYPE) {
                    num2 = car(cdr(args))->i;
                }
                else if(car(cdr(args))->type == DOUBLE_TYPE) {
                    num2 = car(cdr(args))->d;   
                }
                else {
                    evaluationError();   
                }
                subtraction = num1 - num2;  
            }
            else {
                evaluationError();
            }
        }
        else {
            //printf("Not a type\n");
            evaluationError();
        }
        Value* returnValue = makeNull();
        returnValue->type = DOUBLE_TYPE;
        returnValue->d = subtraction;
        return returnValue;
    }
}

// Implements multiplication in Racket, returning errors if there is bad input.
// Works with both INT_TYPE and DOUBLE_TYPE, but will always return a DOUBLE_TYPE Value*.
Value *primitiveMult(Value* args) {
    if(length(args) <= 1) {
        evaluationError();
        return makeNull();
    }
    else {
        double product = 1;
        while (args -> type != NULL_TYPE) {
            if(args->type == CONS_TYPE) {
                if(car(args)->type == INT_TYPE) {
                    product = product * car(args)->i;   
                }
                else if (car(args)->type == DOUBLE_TYPE) {
                    product = product * car(args)->d;   
                }
                else {
                    evaluationError();
                }
                args = cdr(args);
                //}
            }
            else {
                //printf("Not a type\n");
                evaluationError();
            }
        }
        Value* returnValue = makeNull();
        returnValue->type = DOUBLE_TYPE;
        returnValue->d = product;
        return returnValue;
    }
}

// Implements adding in racket, returning errors if there is bad input.
// Works with both INT_TYPE and DOUBLE_TYPE, but will always return a DOUBLE_TYPE Value*
Value *primitiveAdd(Value *args) {
    int count = 0;
    // Set current to be the first value after the '+' operator
    Value* current = cdr(args);
    while(current->type != NULL_TYPE) {
        if(current->type != INT_TYPE && current->type != DOUBLE_TYPE)
        {
            count = count + 1;
            current = cdr(current);
        }
        else {
            //printf("Wrong type of input");
            evaluationError();   
        }
    }
    if (count == 0) {
        Value* zero = makeNull();
        zero->type = INT_TYPE;
        zero->i = 0;
        return zero;
    }
    else { 
        double sum = 0.0;
        while (args->type != NULL_TYPE) {
            if(args->type == CONS_TYPE) {
                
                if(car(args)->type == INT_TYPE) {
                    sum = car(args)->i + sum; 
                    args = cdr(args);
                }
                else if(car(args)->type == DOUBLE_TYPE) {
                    sum = car(args)->d + sum;
                    args = cdr(args);
                }
                else {
                    //printf("Bad type\n");
                    evaluationError();   
                }
            }
            else {
                //printf("Not a type\n");
                evaluationError();
                
            }
        }
        // Evaluate the args one at a time, and apply this to the + function
        Value* newSum = talloc(sizeof(Value));
        newSum->type = DOUBLE_TYPE;
        newSum->d = sum;
        return newSum;
    }
    
}

// Given a linked list, return a Value* of type CONS_TYPE, with the car being
// the car of the linked list, and the cdr being the cdr of the linked list
Value *primitiveCons(Value* args) {
    if(length(args) != 2) {
        // There aren't only two arguments
        //printf("Error - cons does not have 2 arguements");
        evaluationError();   
    }
    
    return cons(car(args), car(cdr(args)));
}

// Given a CONS_CELL, return the car of the CONS_CELL
Value *primitiveCar(Value* args) {
    if(length(args) != 1) {
        //printf("Error - car does not have 1 arguement");
        evaluationError(); 
    }
    
    return car(car(args));
}

// Given a CONS_CELL, return the cdr of the CONS_CELL
Value *primitiveCdr(Value* args) {

    if(length(args) != 1) {
        //printf("Error - cdr does not have 1 arguements");
        evaluationError(); 
    }
    
    return cdr(car(args));
}

// Given a Value*, return a new Value* with BOOL_TYPE. It will return true if
// the args is an empty cons cell, i.e. (), and false otherwise.
Value *primitiveNull(Value* args) {
    if(length(args) != 1) {
        //printf("primitiveNull - not not 1 argument");
        evaluationError();
    }
    Value* output = makeNull();
    output->type = BOOL_TYPE;
    output->i = isNull(car(args));
    
    return output;
}

// Bind a function to a specific sequence of characters
void bind(char *name, Value *(*function)(struct Value *),Frame *frame) {
    // Add primitive functions to top-level bindings list
    Value* value = talloc(sizeof(Value));
    value->type = PRIMITIVE_TYPE;
    value->pf = function;
    
    // Create a new Value* to hold the "key", being the symbol provided
    Value* newFunction = talloc(sizeof(Value));
    newFunction->type = SYMBOL_TYPE;
    newFunction->s = name;
    
    Value* new_binding = makeNull();
    new_binding = cons(value, new_binding);
    new_binding = cons(newFunction,new_binding);

    // Cons the key with the value, which is the function
    frame->bindings = cons(new_binding,frame->bindings);

    // Cons the bindings in the current frame with the newly cons'd function
}

// Creates a new frame, and runs eval() on the given tree and frame.
void interpret(Value *tree){
    
    Frame* frame = talloc(sizeof(Frame));
    frame->bindings = makeNull();
    frame->parent = NULL;
    
    Frame* top_frame = talloc(sizeof(Frame));
    top_frame->bindings = makeNull();
    top_frame->parent = frame;
    
    // Creates bindings for all of the primitive types implemented in our interpreter
    bind("+",primitiveAdd,top_frame);
    bind("cons",primitiveCons,top_frame);
    bind("car",primitiveCar,top_frame);
    bind("cdr",primitiveCdr,top_frame);
    bind("null?",primitiveNull,top_frame);
    bind("*",primitiveMult,top_frame);
    bind("-",primitiveSubtract,top_frame);
    bind("/",primitiveDivide,top_frame);
    bind("%",primitiveModulo,top_frame);
    bind("<",primitiveLessThan,top_frame);
    bind(">",primitiveGreaterThan,top_frame);
    bind("=",primitiveEqualTo,top_frame);
    bind(">=",primitiveGreaterThanEqualTo,top_frame);
    bind("<=",primitiveLessThanEqualTo,top_frame);
    
    while (tree->type!= NULL_TYPE){
        Value* value = eval(car(tree), top_frame);
        if(value->type != VOID_TYPE){
            printValue(value);
            printf("\n");
        }
        tree = cdr(tree);
    }
}

// Given an expression tree and a frame in which to evaluate that expression, eval returns the value of the expression
Value *eval(Value *tree, Frame *frame) {
    switch (tree->type) {
        case INT_TYPE :
            return tree;
            break;
        case STR_TYPE :
            return tree;
            break;
        case BOOL_TYPE :
            return tree;
            break;
        case DOUBLE_TYPE :
            return tree;
            break;
        case CLOSURE_TYPE :
            return tree;
            break;
        case PRIMITIVE_TYPE:
            return tree;
            break;
        case SYMBOL_TYPE :
            return lookUpSymbol(tree, frame);
            break;
        case CONS_TYPE:
            if(car(tree)->type == SYMBOL_TYPE) {
                if (!strcmp(car(tree)->s,"if")) {
                    return evalIf(cdr(tree),frame);
                }
                else if(!strcmp(car(tree)->s,"cond")) {
                    return evalCond(cdr(tree),frame);   
                }

                else if (!strcmp(car(tree)->s,"let")) {
                    return evalLet(cdr(tree),frame);
                }
                 else if (!strcmp(car(tree)->s,"let*")) {
                    return evalLetStar(cdr(tree),frame);
                }else if (!strcmp(car(tree)->s,"letrec")) {
                    return evalLetRec(cdr(tree),frame);
                }
                else if (!strcmp(car(tree)->s,"set!")) {
                    return evalSetBang(cdr(tree),frame);
                }

                // If we encounter a quote symbol we must check to make sure there is only one more argument after
                // it. If this is not the case, we throw an evaluation error

                else if (!strcmp(car(tree)->s,"quote") || !strcmp(car(tree)->s,"\'")) {
                    return evalQuote(cdr(tree),frame);
                } 
                else if (!strcmp(car(tree)->s,"lambda")) {
                    return evalLambda(cdr(tree),frame);
                }
                else if(!strcmp(car(tree)->s,"define")) {
                    return evalDefine(cdr(tree), frame);   
                }
                else if(!strcmp(car(tree)->s,"and")) {
                    return evalAnd(cdr(tree),frame);   
                }
                else if(!strcmp(car(tree)->s,"or")) {
                    return evalOr(cdr(tree),frame);   
                }
                else if(!strcmp(car(tree)->s,"begin")) {
                    return evalBegin(cdr(tree),frame);   
                }
                else {
                    Value *evaledOperator = eval(car(tree), frame);

                    Value *evaledArgs = evalEach(cdr(tree), frame);
                    return apply(evaledOperator,evaledArgs);
                }
            }
            else {
                return tree;
            }
            // Sanity and error checking on first...
            break;
        case NULL_TYPE:
            return tree;
            break;
        default:
            //printf("Eval - not a value type\n");
            evaluationError();      
    }    
    evaluationError();
    Value *nullThing = makeNull();
    return nullThing;
}

// Prints the correct output, given a Value*
void printValue(Value* value){
    if(value->type == NULL_TYPE) {
        printf("()");
    }
    else if(value->type == INT_TYPE) {
        printf("%i",value->i);   
    }
    else if(value->type == STR_TYPE) {
        printf("\"%s\"",value->s);   
    }
    else if(value->type == DOUBLE_TYPE) {
        printf("%f",value->d);   
    }
    else if(value->type == BOOL_TYPE) {
        if(value->i == 0) {
            printf("#f");
        }
        else {
            printf("#t");   
        }
    }
    else if(value->type == SYMBOL_TYPE) {
        if (!strcmp(value->s,"quote") || !strcmp(value->s,"\'")){
            printf("\'");
        }else{
            printf("%s",value->s);  
        }
    
    }else if(value->type == OPEN_TYPE) {
        printf("(");   
    }else if(value->type == CLOSE_TYPE) {
        printf(")");   
    }else if(value->type == CONS_TYPE) {
        
        if (cdr(value)->type != CONS_TYPE && cdr(value)->type != NULL_TYPE ){
            
            printf("(");
            printValue(car(value));
            printf(" . ");
            printValue(cdr(value));
            printf(")");
        }else{
            printf("(");
            printTree(value);
            printf(")");
        }
        
    }else if(value->type == CLOSURE_TYPE) {
        printf("#<procedure>");
    }else if(value->type == VOID_TYPE) {
    }else{
        //printf("\n ERROR- not a value \n");
    }

}

// This is essentially the same as printTree from parser.c, but has been modified
// so that we can print in the racket style
// In input.5, we need to fix (quote a) so that it returns 'a and not a
void printTree_2(Value* value) {
    while (value->type != NULL_TYPE){
        if (car(value)->type == CONS_TYPE){
            if (!strcmp(car(car(value))->s,"quote") || !strcmp(car(car(value))->s,"\'")){
                printf("#\n");
                printf(" ");
                printTree(car(value)); printf("\n");
                printTree_2(car(value));
            }
            else {
                printf("!\n");
                printf("(");
                printTree_2(car(value));
                printf(")");
            } 
        }else {
            printValue(car(value));  
        }
        if(cdr(value)->type != NULL_TYPE) {  
            if (car(cdr(value))->type != CONS_TYPE){
                printf(" ");
            }
        }   
        value = cdr(value);
    } 
}