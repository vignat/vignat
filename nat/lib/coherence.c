#include "coherence.h"

/*@
  predicate dmap_dchain_coherent<t1,t2,vt>(dmap<t1,t2,vt> m, dchain ch) =
    dchain_index_range_fp(ch) == dmap_cap_fp(m) &*&
    true == subset(dchain_indexes_fp(ch), dmap_indexes_used_fp(m)) &*&
    true == subset(dmap_indexes_used_fp(m), dchain_indexes_fp(ch));
  @*/

/*@

lemma void empty_dmap_dchain_coherent<t1,t2,vt>(int len)
requires 0 <= len;
ensures dmap_dchain_coherent<t1,t2,vt>
         (empty_dmap_fp<t1,t2,vt>(len), empty_dchain_fp(len, 0));
{
  empty_dmap_cap<t1,t2,vt>(len);
  dmap_empty_no_indexes_used<t1,t2,vt>(len);
  close dmap_dchain_coherent(empty_dmap_fp<t1,t2,vt>(len),
                             empty_dchain_fp(len, 0));
}

lemma void coherent_dmap_used_dchain_allocated<t1,t2,vt>
             (dmap<t1,t2,vt> m, dchain ch, int idx)
requires dmap_dchain_coherent(m, ch) &*& dmap_index_used_fp(m, idx) == true;
ensures dmap_dchain_coherent(m, ch) &*&
        dchain_allocated_fp(ch, idx) == true;
{
  open dmap_dchain_coherent(m, ch);
  dmap_index_used_inbounds(m, idx);
  dmap_indexes_contain_index_used(m, idx);
  mem_subset(idx, dmap_indexes_used_fp(m), dchain_indexes_fp(ch));
  dchain_indexes_contain_index(ch, idx);
  close dmap_dchain_coherent(m, ch);
}

lemma void expire_preserves_coherent<t1,t2,vt>
             (dmap<t1,t2,vt> m, dchain ch, uint32_t time,
              fixpoint (vt,t1) vk1,
              fixpoint (vt,t2) vk2)
requires dmap_dchain_coherent(m, ch);
ensures dmap_dchain_coherent(dmap_erase_all_fp
                                (m, dchain_get_expired_indexes_fp(ch, time),
                                vk1, vk2),
                             dchain_expire_old_indexes_fp(ch, time));
{
  assume(false);//TODO
}

lemma void dchain_rejuvenate_preserves_indexes_set(dchain ch, int index,
                                                   uint32_t time)
requires true;
ensures true == subset(dchain_indexes_fp(ch),
                       dchain_indexes_fp(dchain_rejuvenate_fp(ch, index,
                                                              time))) &*&
        true == subset(dchain_indexes_fp(dchain_rejuvenate_fp(ch, index,
                                                              time)),
                       dchain_indexes_fp(ch));
{
  assume(false);//TODO
}

lemma void rejuvenate_preserves_coherent<t1,t2,vt>
             (dmap<t1,t2,vt> m, dchain ch,
              int index, uint32_t time)
requires dmap_dchain_coherent(m, ch);
ensures dmap_dchain_coherent(m, dchain_rejuvenate_fp(ch, index, time));
{
  open dmap_dchain_coherent(m, ch);
  dchain_rejuvenate_preserves_indexes_set(ch, index, time);
  rejuvenate_preserves_index_range(ch, index, time);
  dchain nch = dchain_rejuvenate_fp(ch, index, time);
  subset_trans(dchain_indexes_fp(nch), dchain_indexes_fp(ch),
               dmap_indexes_used_fp(m));
  subset_trans(dmap_indexes_used_fp(m), dchain_indexes_fp(ch),
               dchain_indexes_fp(nch));
  close dmap_dchain_coherent(m, nch);
}

lemma void coherent_put_allocated_preserves_coherent<t1,t2,vt>
(dmap<t1,t2,vt> m, dchain ch, t1 k1, t2 k2,
 vt value, int ind, uint32_t t,
 fixpoint (vt,t1) vk1,
 fixpoint (vt,t2) vk2)
requires dmap_dchain_coherent(m, ch) &*& false == dchain_allocated_fp(ch, ind);
ensures dmap_dchain_coherent(dmap_put_fp(m, ind, value, vk1, vk2),
                             dchain_allocate_fp(ch, ind, t));
{
  assume(false);//TODO
}

@*/

/*@
  lemma void distinct_subset_sublen<t>(list<t> xs, list<t> ys)
  requires true == distinct(xs) &*&
           true == subset(xs, ys);
  ensures length(xs) <= length(ys);
  {
    assume(false);//TODO
  }
  @*/

/*@
  lemma void dchain_out_of_space_to_indexes_size(dchain ch)
  requires true;
  ensures dchain_out_of_space_fp(ch) ==
          (dchain_index_range_fp(ch) <= length(dchain_indexes_fp(ch)));
  {
    assume(false);//TODO
  }
  @*/

/*@
  lemma void dmap_size_of_indexes_used<t1,t2,vt>(dmap<t1,t2,vt> m)
  requires true;
  ensures dmap_size_fp(m) == length(dmap_indexes_used_fp(m));
  {
    assume(false);//TODO
  }
  @*/

/*@

lemma void coherent_dchain_non_out_of_space_map_nonfull<t1,t2,vt>
            (dmap<t1,t2,vt> m, dchain ch)
requires dmappingp<t1,t2,vt>(m, ?a, ?b, ?c, ?d, ?e, ?g, ?h, ?i, ?j, ?k, ?l, ?n, ?f) &*&
         dmap_dchain_coherent(m, ch) &*&
         dchain_out_of_space_fp(ch) == false;
ensures dmappingp<t1,t2,vt>(m, a, b, c, d, e, g, h, i, j, k, l, n, f) &*&
        dmap_dchain_coherent(m, ch) &*&
        dmap_size_fp(m) < dmap_cap_fp(m);
{
  open dmap_dchain_coherent(m, ch);

  dmap_indexes_used_distinct(m);
  distinct_subset_sublen(dmap_indexes_used_fp(m), dchain_indexes_fp(ch));
  dchain_out_of_space_to_indexes_size(ch);
  dmap_size_of_indexes_used(m);

  close dmap_dchain_coherent(m, ch);
}

@*/

/*@
  lemma void coherent_expire_one<t1,t2,vt>(dmap<t1,t2,vt> m,
                                           dchain ch,
                                           int idx,
                                           fixpoint (vt,t1) vk1,
                                           fixpoint (vt,t2) vk2)
  requires dmap_dchain_coherent(m, ch) &*&
           dchain_nodups(ch) &*&
           true == dchain_allocated_fp(ch, idx) &*&
           0 <= idx;
  ensures dmap_dchain_coherent(dmap_erase_fp(m, idx, vk1, vk2),
                               dchain_remove_index_fp(ch, idx)) &*&
          dchain_nodups(dchain_remove_index_fp(ch, idx));
  {
    open dmap_dchain_coherent(m, ch);
    dmap<t1,t2,vt> nm = dmap_erase_fp(m, idx, vk1, vk2);
    dchain nch = dchain_remove_index_fp(ch, idx);
    dchain_remove_keeps_ir(ch, idx);
    dmap_erase_keeps_cap(m, idx, vk1, vk2);
    assert dchain_index_range_fp(nch) == dmap_cap_fp(nm);
    dchain_remove_idx_from_indexes(ch, idx);
    assert dchain_indexes_fp(nch) ==
           remove(idx, dchain_indexes_fp(ch));
    dmap_erase_removes_index(m, idx, vk1, vk2);
    assert dmap_indexes_used_fp(nm) ==
           remove(idx, dmap_indexes_used_fp(m));

    dchain_nodups_unique_idx(ch, idx);
    dmap_indexes_used_distinct(m);
    distinct_mem_remove(idx, dmap_indexes_used_fp(m));
    remove_both_subset(idx, dchain_indexes_fp(ch), dmap_indexes_used_fp(m));
    remove_both_subset(idx, dmap_indexes_used_fp(m), dchain_indexes_fp(ch));

    dchain_remove_keeps_nodups(ch, idx);

    close dmap_dchain_coherent(nm, nch);
  }
  @*/

/*@
  lemma void coherent_same_cap<t1,t2,vt>(dmap<t1,t2,vt> m, dchain ch)
  requires dmap_dchain_coherent(m, ch);
  ensures dmap_dchain_coherent(m, ch) &*&
          dmap_cap_fp(m) == dchain_index_range_fp(ch);
  {
    open dmap_dchain_coherent(m, ch);
    close dmap_dchain_coherent(m, ch);
  }
  @*/

/*@
  lemma void coherent_old_index_used<t1,t2,vt>(dmap<t1,t2,vt> m, dchain ch)
  requires dmap_dchain_coherent(m, ch) &*&
           false == dchain_is_empty_fp(ch) &*&
           0 <= dchain_get_oldest_index_fp(ch) &*&
           dchain_get_oldest_index_fp(ch) < dchain_index_range_fp(ch);
  ensures dmap_dchain_coherent(m, ch) &*&
          true == dmap_index_used_fp(m, dchain_get_oldest_index_fp(ch));
  {
    dchain_oldest_allocated(ch);
    coherent_same_cap(m, ch);
    open dmap_dchain_coherent(m, ch);
    dchain_indexes_contain_index(ch, dchain_get_oldest_index_fp(ch));
    mem_subset(dchain_get_oldest_index_fp(ch), dchain_indexes_fp(ch),
               dmap_indexes_used_fp(m));
    dmap_indexes_contain_index_used(m, dchain_get_oldest_index_fp(ch));
    close dmap_dchain_coherent(m, ch);
  }
  @*/
