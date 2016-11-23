#include "llvm/ADT/APInt.h"
#include "llvm/IR/ConstantRange.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/NoFolder.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>
#include <iostream>
#include <stdio.h>
#include <sstream>
#include <cerrno>

using namespace llvm;
using namespace std;


enum Token {
  tok_arg,
  tok_arithop,
  tok_eof,
  tok_id,
  tok_lparen,
  tok_compop,
  tok_rparen,
  tok_number
} typedef Token;

template<typename T>
runtime_error throw_err(string message, T item) {
  std::ostringstream err_msg;
  err_msg << message << item;
  return runtime_error(err_msg.str());
}

class Lexer {
  private:
    int index = 0;
    std::string &input;

    bool iscomp(char c) {
      return ('<' <= c && c <= '>') || c == '!';
    }

    char getchar() {
      return input.at(index++);
    }

    void goback() {
      index -= 1;
    }

    char lookahead() {
      return input.at(index);
    }

    char lookbehind() {
      if (index-2 >= 0) {
        return input.at(index-2);
      }
      else {
        return '\n';
      }
    }

  public:
    long numval;
    int argnum = -1;
    char arithop = -1;
    string id = "";
    string compop = "";

    Lexer(std::string &inputarg) : input(inputarg) {};

    Token gettok() {
      char current_char = getchar();

      while(isspace(current_char)) {
        current_char = getchar();
      }

      // handle comments - currently allows comments not starting at start of line
      if (current_char == '#' && lookbehind() == '\n') {
        current_char = getchar();
        while(current_char != '\n') {
          if (current_char == EOF) {
            return tok_eof;
          }
          current_char = getchar();
        }
        return gettok();
      }

      if (isdigit(current_char) || (current_char == '-' && isdigit(lookahead()))) {
        std::string numstr;
        do {
          numstr += current_char;
          current_char = getchar();
        } while (isdigit(current_char));

        numval = strtol(numstr.c_str(), nullptr, 10);
        if (errno == ERANGE) {
          throw throw_err("Number out of range: ", numstr);
        }
        goback();
        return tok_number;
      }

      if (current_char == '(') {
        return tok_lparen;
      }

      if (current_char == ')') {
        return tok_rparen;
      }

      if (current_char == 'a') {
        char next = getchar();
        if('0' <= next && next <= '5') {
          char s[2] = {next, '\0'};
          argnum = strtod(s, nullptr);
          return tok_arg;
        }
        else {
          throw throw_err("Not a valid argument name: a", next);
        }
        return tok_arg;
      }

      if (isalpha(current_char)) {
        id = "";
        do {
          id += current_char;
          current_char = getchar();
        } while (isalpha(current_char));

        goback();
        return tok_id;
      }

      if (iscomp(current_char)) {
        compop = "";
        compop += current_char;
        if(iscomp(lookahead())) {
          compop += getchar();
        }

        return tok_compop;
      }

      if (current_char == '+' ||
          current_char == '-' ||
          current_char == '/' ||
          current_char == '%' ||
          current_char == '*') {
        arithop = current_char;
        return tok_arithop;
      }

      if (current_char == EOF) {
        return tok_eof;
      }

      throw throw_err("Lexer error on: ", current_char);
    }

    string format_token(Token value) {
      std::ostringstream result;
      switch (value) {
        case (tok_arg) : result << "arg: " << argnum; break;
        case (tok_arithop) : result << "arithmetic op: " << arithop; break;
        case (tok_compop) : result << "comparison op: " << compop; break;
        case (tok_eof) : result << "EOF"; break;
        case (tok_id) : result << "id: " << id; break;
        case (tok_lparen) : result << "lparen"; break;
        case (tok_number) : result << "number: " << numval; break;
        case (tok_rparen) : result << "rparen"; break;
      }
      return result.str();
    }
};

class Parser {
  private:
    Lexer &l;
    int counter = 0;
    LLVMContext &C;
    IRBuilder<NoFolder> &B;
    Function *F;
    std::vector<Value*> &Arguments;
    std::vector<Value*> &Mutables;

    string gensym() {
      std::ostringstream name;
      name << 't';
      name << counter++;
      return name.str();
    }

  public:
    Parser(Lexer &lex, IRBuilder<NoFolder> &Barg, LLVMContext &Carg, std::vector<Value*> &Args, Function *Farg, std::vector<Value*> &Muts) : l(lex), B(Barg), C(Carg), Arguments(Args), Mutables(Muts), F(Farg) {};

    Value* parse() {
      Token t = l.gettok();

      if (t == tok_number) {
        return ConstantInt::get(C, APInt(64, l.numval));
      }

      if (t == tok_arg) {
        return Arguments[l.argnum];
      }

      if (t == tok_lparen) {
        t = l.gettok();

        if (t == tok_arithop) {
          char op = l.arithop;
          llvm::Value* lhs = parse();
          llvm::Value* rhs = parse();
          check_rparen();
          switch(op) {
            case '+':
              return B.CreateNUWAdd(lhs, rhs);
            case '-':
              return B.CreateNUWSub(lhs, rhs);
            case '*':
              return B.CreateNUWMul(lhs, rhs);
            case '/':
              return B.CreateSDiv(lhs, rhs);
            case '%':
              return B.CreateSRem(lhs, rhs);

          }
          throw runtime_error("This should not be reachable");
        }
        else if (t == tok_id && l.id == "if") {
          BasicBlock *BB1 = BasicBlock::Create(C, "cond1", F);
          BasicBlock *BB2 = BasicBlock::Create(C, "cond2", F);
          BasicBlock *BB3 = BasicBlock::Create(C, "merge", F);

          llvm::Value* boolcond = parseBool();
          B.CreateCondBr(boolcond, BB1, BB2);

          B.SetInsertPoint(BB1);
          llvm::Value* exp1 = parse();
          BasicBlock *e1block = B.GetInsertBlock();
          B.CreateBr(BB3);

          B.SetInsertPoint(BB2);
          llvm::Value* exp2 = parse();
          BasicBlock *e2block = B.GetInsertBlock();
          B.CreateBr(BB3);

          B.SetInsertPoint(BB3);
          PHINode* phi = B.CreatePHI(Type::getInt64Ty(C), 2);
          phi->addIncoming(exp1, e1block);
          phi->addIncoming(exp2, e2block);
          check_rparen();

          return phi;
        }
        else {
          throw throw_err("Expected 'if' or arithmetic operator but found: ", l.format_token(t));
        }
      }

      throw throw_err("Invalid start of arithmetic expression: ", l.format_token(t));
    }
    Value* parseBool() {
      Token t = l.gettok();
      if (t == tok_lparen) {
        t = l.gettok();
        if (t == tok_compop) {
          string op = l.compop;
          llvm::Value* lhs = parse();
          llvm::Value* rhs = parse();
          check_rparen();
          if (op == ">=") {
            return B.CreateICmpSGE(lhs, rhs);
          }
          else if (op == "<=") {
            return B.CreateICmpSLE(lhs, rhs);
          }
          else if (op == "==") {
            return B.CreateICmpEQ(lhs, rhs);
          }
          else if (op == "!=") {
            return B.CreateICmpNE(lhs, rhs);
          }
          else if (op == "<") {
            return B.CreateICmpSLT(lhs, rhs);
          }
          else if (op == ">") {
            return B.CreateICmpSGT(lhs, rhs);
          }
          else if (op == ">=") {
            return B.CreateICmpSGE(lhs, rhs);
          }
          else {
            throw throw_err("Invalid operation: ", op);
          }
        }
        else {
          throw throw_err("Expected comparison operator but found: ", l.format_token(t));
        }
      }
      else if (t == tok_id && l.id == "true") {
        return ConstantInt::get(C, APInt(1, 1));
      }
      else if (t == tok_id && l.id == "false") {
        return ConstantInt::get(C, APInt(1, 0));
      }
      else {
        throw throw_err("Invalid start of boolean expression; found: ", l.format_token(t));
      }
    }

    void check_rparen() {
      Token t = l.gettok();
      if (t != tok_rparen) {
        throw throw_err("Expected ')' but found: ", l.format_token(t));
      }
    }
};



/// top ::= definition | external | expression | ';'
//static void MainLoop() {
//while (true) {
//// fprintf(stderr, "ready> ");
//switch (CurTok) {
//case tok_eof:
//printf("EOM");
//return;
//case tok_number:
//printf("number");
////case ';': // ignore top-level semicolons.
////  getNextToken();
////  break;
////case tok_def:
////  HandleDefinition();
////  break;
////case tok_extern:
////  HandleExtern();
////  break;
//default:
//printf("default");
////break;
//return;
//}
//}
//}

static int compile() {
  LLVMContext C;
  IRBuilder<NoFolder> Builder(C);
  std::unique_ptr<Module> M = llvm::make_unique<Module>("calc", C);

  M->setTargetTriple(llvm::sys::getProcessTriple());
  std::vector<Type *> SixInts(6, Type::getInt64Ty(C));
  FunctionType *FT = FunctionType::get(Type::getInt64Ty(C), SixInts, false);
  Function *F = Function::Create(FT, Function::ExternalLinkage, "f", &*M);
  BasicBlock *BB = BasicBlock::Create(C, "entry", F);
  Builder.SetInsertPoint(BB);

  std::vector<Value*> args;
  std::vector<Value*> mutables;

  for (auto &arg : F->args()) {
    args.push_back(&arg);
  }

  for (int i = 0; i < 10; i++) {
    mutables.push_back(Builder.CreateAlloca(Type::getInt64Ty(C)));
  }

  std::ostringstream std_input;
  std_input << std::cin.rdbuf() << ((char) EOF);
  std::string s = std_input.str();

  Value *RetVal;



  try {
    Lexer l = Lexer(s);
    Parser p = Parser(l, Builder, C, args, F, mutables);
    RetVal = p.parse();
    Token t = l.gettok();
    if (t != tok_eof) {
      throw throw_err("Expected EOF but found: ", l.format_token(t));
    }
  }
  catch (std::exception &e) {
    std::cerr << "caught exception: " << e.what() << std::endl;
    return 1;
  }


  // TODO: generate correct LLVM instead of just an empty function

  //Value *RetVal = ConstantInt::get(C, APInt(64, 0));
  Builder.CreateRet(RetVal);
  M->dump();
  assert(!verifyModule(*M));
  return 0;
}


int main(void) { return compile(); }
