// verifast_options{fwrapv}

#include <stdlib.h>
#include <stdio.h>

struct expr;
typedef struct expr *expr;

struct literal_expr_info {
  int value;
};

struct binop_expr_info {
  char operator;
  expr leftOperand;
  expr rightOperand;
};

enum expr_tag { EXPR_TAG_LITERAL, EXPR_TAG_BINOP };

union expr_info {
  struct literal_expr_info literal;
  struct binop_expr_info binop;
};

struct expr {
  enum expr_tag tag;
  union expr_info info;
};

/*@

predicate expr(expr e;) =
  malloc_block_expr(e) &*&
  e->tag |-> ?tag &*&
  tag == EXPR_TAG_LITERAL ?
    e->info.literal.value |-> ?_ &*&
    struct_literal_expr_info_padding(&e->info.literal) &*&
    chars_((void *)&e->info + sizeof(struct literal_expr_info), sizeof(union expr_info) - sizeof(struct literal_expr_info), _)
  : tag == EXPR_TAG_BINOP ?
    e->info.binop.operator |-> ?_ &*&
    e->info.binop.leftOperand |-> ?e1 &*& expr(e1) &*&
    e->info.binop.rightOperand |-> ?e2 &*& expr(e2) &*&
    struct_binop_expr_info_padding(&e->info.binop) &*&
    chars_((void *)&e->info + sizeof(struct binop_expr_info), sizeof(union expr_info) - sizeof(struct binop_expr_info), _)
  : false;

@*/

expr mk_literal_expr(int value)
//@ requires true;
//@ ensures expr(result);
{
  expr result = malloc(sizeof(struct expr));
  if (result == 0) abort();
  result->tag = EXPR_TAG_LITERAL;
  //@ char__limits((void *)&result->info);
  result->info./*@activating@*/literal.value = value;
  return result;
}

expr mk_binop_expr(char operator, expr leftOperand, expr rightOperand)
//@ requires expr(leftOperand) &*& expr(rightOperand);
//@ ensures expr(result);
{
  expr result = malloc(sizeof(struct expr));
  if (result == 0) abort();
  result->tag = EXPR_TAG_BINOP;
  result->info./*@activating@*/binop.operator = operator;
  result->info.binop.leftOperand = leftOperand;
  result->info.binop.rightOperand = rightOperand;
  return result;
}

int eval(expr e)
//@ requires expr(e);
//@ ensures expr(e);
{
  switch (e->tag) {
    case EXPR_TAG_LITERAL:
      return e->info.literal.value;
    case EXPR_TAG_BINOP:
      {
        int v1 = eval(e->info.binop.leftOperand);
        int v2 = eval(e->info.binop.rightOperand);
        switch (e->info.binop.operator) {
          case '+': return /*@truncating@*/ (v1 + v2);
          case '-': return /*@truncating@*/ (v1 - v2);
          default: abort();
        }
      }
  }
}

void dispose(expr e)
//@ requires expr(e);
//@ ensures true;
{
  switch (e->tag) {
    case EXPR_TAG_LITERAL:
      //@ deactivate_union_member(e->info.literal);
      free(e);
      break;
    case EXPR_TAG_BINOP:
      dispose(e->info.binop.leftOperand);
      dispose(e->info.binop.rightOperand);
      //@ deactivate_union_member(e->info.binop);
      free(e);
      break;
  }
}

int main()
//@ requires true;
//@ ensures true;
{
  expr e10 = mk_literal_expr(10);
  expr e20 = mk_literal_expr(20);
  expr e10plus20 = mk_binop_expr('+', e10, e20);
  expr e25 = mk_literal_expr(25);
  expr e10plus20minus25 = mk_binop_expr('-', e10plus20, e25);
  int value = eval(e10plus20minus25);
  printf("%d\n", value);
  dispose(e10plus20minus25);
  return 0;
}
