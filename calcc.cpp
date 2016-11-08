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

using namespace llvm;
using namespace std;

static LLVMContext C;
static IRBuilder<NoFolder> Builder(C);
static std::unique_ptr<Module> M = llvm::make_unique<Module>("calc", C);

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

  public:
    int numval;
    string argname = "";
    string arithop = "";
    string id = "";
    string compop = "";

    Lexer(std::string &inputarg) : input(inputarg) {};

    Token gettok() {
      char current_char = getchar();

      while(isspace(current_char)) {
        current_char = getchar();
      }

      // handle comments - currently allows comments not starting at start of line
      if (current_char == '#') {
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

        numval = strtod(numstr.c_str(), nullptr);
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
        argname = "a";
        char next = getchar();
        if('0' <= next && next <= '5') {
          argname += next;
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
          current_char == '\\' ||
          current_char == '%' ||
          current_char == '*') {
        arithop = "";
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
        case (tok_arg) : result << "arg: " << argname; break;
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

    string gensym() {
      std::ostringstream name;
      name << 't';
      name << counter++;
      return name.str();
    }

  public:
    Parser(Lexer &lex) : l(lex) {};

    string parse() {
      Token t = l.gettok();

      if (t == tok_number) {
        return std::to_string(l.numval);
      }

      if (t == tok_arg) {
        return l.argname;
      }

      if (t == tok_lparen) {
        t = l.gettok();

        if (t == tok_arithop) {
          string op = l.arithop;
          string lhs = parse();
          string rhs = parse();
          check_rparen();
          std::ostringstream res;
          string gs = gensym();
          res << gs << " := " << lhs << ' ' << op << ' ' << rhs;
          std::cout << res.str() << std::endl;
          return gs;
        }
        else if (t == tok_id && l.id == "if") {
          string op = l.arithop;
          string B = parseBool();
          string exp1 = parse();
          string exp2 = parse();
          check_rparen();
          std::ostringstream res;
          string gs = gensym();
          res << gs << " := " << " IF " << B << ' ' << exp1 << " ELSE " << exp2;
          std::cout << res.str() << std::endl;
          return gs;
        }
        else {
          throw throw_err("Expected 'if' or arithmetic operator but found: ", l.format_token(t));
        }
      }

    throw throw_err("Invalid start of arithmetic expression: ", l.format_token(t));
    }
// (if true 1 2)
// (if (> 2 1) 1 2)
    string parseBool() {
      Token t = l.gettok();
      if (t == tok_lparen) {
        t = l.gettok();
        if (t == tok_compop) {
         string op = l.compop;
         string lhs = parse();
         string rhs = parse();
         check_rparen();
         std::ostringstream res;
         string gs = gensym();
         res << gs << " := " << lhs << ' ' << op << ' ' << rhs;
         std::cout << res.str() << std::endl;
         return gs;
        }
        else {
          throw throw_err("Expected comparison operator but found: ", l.format_token(t));
        }
      }
      else if (t == tok_id && (l.id == "false" || l.id == "true")) {
        return l.id;
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
  //M->setTargetTriple(llvm::sys::getProcessTriple());
  //std::vector<Type *> SixInts(6, Type::getInt64Ty(C));
  //FunctionType *FT = FunctionType::get(Type::getInt64Ty(C), SixInts, false);
  //Function *F = Function::Create(FT, Function::ExternalLinkage, "f", &*M);
  //BasicBlock *BB = BasicBlock::Create(C, "entry", F);
  //Builder.SetInsertPoint(BB);
  std::ostringstream std_input;
  std_input << std::cin.rdbuf() << ((char) EOF);
  std::string s = std_input.str();


  try {
    Lexer l = Lexer(s);
    Parser p = Parser(l);
    std::cout << p.parse() << std::endl;
    Token t = l.gettok();
    if (t != tok_eof) {
      throw throw_err("Expected EOF but found: ", l.format_token(t));
    }
  }
  catch (std::exception &e) {
    std::cerr << "caught exception: " << e.what() << std::endl;
  }

  /*try {
    while(true) {
      Lexer::Token t = l.gettok();
      //std::cout << t << std::endl;
      std::cout << l.format_token(t) << std::endl;
      if(t == Lexer::tok_eof) { break; }
    }
  }
  catch (std::exception &e) { std::cerr << "caught exception: " << e.what() << std::endl; }
  */

  // TODO: generate correct LLVM instead of just an empty function

  //Value *RetVal = ConstantInt::get(C, APInt(64, 0));
  //Builder.CreateRet(RetVal);
  //assert(!verifyModule(*M));
  //M->dump();

  return 0;
}


int main(void) { return compile(); }
