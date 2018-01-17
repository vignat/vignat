
#include <limits.h>
#include <stdlib.h>

struct List {
    int value;
    struct List* next;
};

/*@ inductive reachable{L}(struct List* root, struct List* to) {
  @   case empty{L}: \forall struct List* l; reachable(l, l);
  @   case non_empty{L}: \forall struct List *l1,*l2;
  @     \valid(l1) && reachable(l1->next, l2) ==> reachable(l1, l2);
  @ }
*/

/*@ inductive sublist{L}(struct List* l1, struct List* l2) {
  @   case same{L}: \forall struct List *l1; sublist(l1, l1);
  @   case step{L}: \forall struct List *l1, *l2;
  @      sublist(l1->next, l2) ==> sublist(l1, l2);
  @ }
*/

#if 0
/*@ logic integer length_l{L}(struct List* root) =
  @   (root == \null) ? 0 :
  @   1 + length_l(root->next);
*/

/*@ lemma len_next: \forall struct List* l;
  @    l != \null && reachable(l, \null) ==>
  @       length_l(l) == length_l(l->next) + 1;
*/

/*@ lemma len_zero: length_l(\null) == 0;
 */

/*@ lemma len_less: \forall struct List* l;
  @    \valid(l) ==> length_l(l->next) < length_l(l);
*/

#endif

/*@ axiomatic List_length {
  @ logic integer length_l{L}(struct List* root)
  @   reads *({ l | struct List* l; reachable(root, l)});
  @
  @ axiom len_next: \forall struct List* l;
  @   \valid(l)  ==>
  @   length_l(l) == length_l(l->next) + 1;
  @
  @ axiom len_zero: length_l(\null) == 0;
  @
  @ axiom len_sub_list: \forall struct List *l1, *l2;
  @    sublist(l1, l2) ==> length_l(l1) >= length_l(l2);
  @
  @ axiom len_non_neg: \forall struct List* l; 
  @    reachable(l, \null) ==> length_l(l) >= 0;
  @ }
 */

/*@ lemma len_less: \forall struct List* l;
  @   \valid(l) ==> length_l(l->next) < length_l(l);
*/

//CoQ: admit.
/*@ lemma next_null_reachable: \forall struct List* l;
  @   \valid(l) && reachable(l, \null) ==> reachable(l->next, \null);
*/


/*@ requires \valid(l);
  @ requires \forall struct List* l1, struct List* l2;
  @    reachable(l, l1) && reachable(l, l2) ==>
  @       l1 == l2 || \separated(l1, l2);
  @ requires \forall struct List* l1;
  @    reachable(l, l1) ==> l1 == \null || \valid(l1);
  @ requires reachable(l, \null);
  @ requires length_l(l) < INT_MAX;
  @ assigns \nothing;
  @ ensures \result >= 0;
  @ ensures \result == length_l(l);
*/
int length(struct List* l) {
    struct List* i = l;
    int ret = 0;
    /*@ loop invariant \forall struct List* l1;
      @      reachable(i, l1) ==> l1 == \null || \valid(l1);
      @ loop invariant reachable(i, \null);
      @ loop invariant ret >= 0;
      @ loop invariant ret + length_l(i) == length_l(l);
      @ loop invariant ret <= length_l(l);
      @ loop invariant length_l(i) >= 0;
      @ loop invariant length_l(l) < INT_MAX;
      @ loop assigns ret;
      @ loop assigns i;
      @ loop variant length_l(i);
    */
    while (i != 0) {
        //@ assert(\valid(i));
        ret ++;
        i = i->next;
    }
    //@ assert(length_l(i) == 0);
    //@ assert(ret == length_l(l));
    return ret;
}


/*@ predicate contains{L}(struct List* l, int val) = \exists struct List* x;
  @     reachable(l, x) && \valid(x) && x->value == val;
*/

/*@ predicate correct_list{L}(struct List* l) = 
  @   reachable(l, \null) && (\forall struct List* x; reachable(l, x) ==>
  @     (x == \null) || (\valid(x) && \freeable(x)));
*/

//What's about the 'assigns' ?
/*@ requires \valid(l) || l == \null;
  @ requires reachable(l, \null);
  @ behavior success:
  @   assumes is_allocable((unsigned int)sizeof(struct List));
  @   ensures \result != \null;
  @   ensures contains(\result, val);
  @   ensures length_l(\result) == length_l(l) + 1;
  @   ensures reachable(\result, \null);
  @ behavior no_memory:
  @   assumes !is_allocable((unsigned int)sizeof(struct List));
  @   ensures \result == \null;
  @ complete behaviors;
  @ disjoint behaviors;
 */
struct List* push_front(struct List* l, int val) {
    struct List* ret = (struct List*)malloc(sizeof(struct List));
    if (ret) {
        //@ assert(\valid(ret)); 
        ret->value = val;
        ret->next = l;
    }
    return ret;    
}

/*@ requires \valid(l);
  @ requires correct_list(l);
  @ requires reachable(l, \null);
  @ frees l;
  @ ensures reachable(\result, \null);
  @ ensures length_l(\result) == length_l(l) - 1;
*/
struct List* pop_front(struct List* l, int val) {
    struct List* ret = l->next;
    free(l);
    return ret;
}
