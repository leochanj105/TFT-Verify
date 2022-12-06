from z3 import *
import sys

def P(str):
    return Bool(str)

def maintain(st, step, peer, state):
    return st[step + 1][peer][state] == st[step][peer][state]


def update_joined_before(st, step, peer):
    return st[step + 1][peer]["joined_before"] == Or(st[step][peer]["joined_before"], st[step + 1][peer]["joined"])

def update_left_after_joined(st, step, peer):
    return st[step + 1][peer]["left_after_joined"] == And(st[step + 1][peer]["joined_before"], 
                                                          Or(st[step][peer]["left_after_joined"],
                                                             st[step + 1][peer]["left"]))
def main(num_peers = 2):
    num_steps = 7 ** num_peers
    # num_steps = 16 ** num_peers
    s = Solver()
    st = []
    for step in range(num_steps):
        peer_states = []
        for peer in range(num_peers):
            per_peer_st = dict()
            per_peer_st["joined"] = P("step{}_peer{}_joined".format(step, peer))
            per_peer_st["left"] = P("step{}_peer{}_left".format(step, peer))
            per_peer_st["holds"] = P("step{}_peer{}_holds".format(step, peer))
            per_peer_st["has_sent"] = P("step{}_peer{}_has_sent".format(step, peer))
            per_peer_st["joined_before"] = P("step{}_peer{}_joined_before".format(step, peer))
            per_peer_st["left_after_joined"] = P("step{}_peer{}_left_after_joined".format(step, peer))
            peer_states.append(per_peer_st)
        st.append(peer_states)
    
    # Add initial constraints
    
    s.add(st[0][0]["joined"])
    s.add(st[0][0]["holds"])
    for peer in range(num_peers):
        s.add(Not(st[0][peer]["left"]))
        s.add(Not(st[0][peer]["has_sent"]))
        s.add(st[0][peer]["joined_before"] == st[0][peer]["joined"])
        s.add(Not(st[0][peer]["left_after_joined"]))

    for step in range(num_steps - 1):
        event_list = []
        preconditions = []
        for p1 in range(num_peers):
            for p2 in range(num_peers):
                # send(p1, p2) event
                pre_send = And(st[step][p1]["joined"], 
                               st[step][p2]["joined"], 
                               st[step][p1]["holds"], 
                               Not(st[step][p2]["holds"]))
                preconditions.append(pre_send)
                post_send = []
                for peer in range(num_peers):
                    if peer == p1:
                        post_send.append(st[step + 1][peer]["has_sent"])
                    else:
                        post_send.append(maintain(st, step, peer, "has_sent"))
                    if peer == p2:
                        post_send.append(st[step + 1][peer]["holds"])
                    else:
                        post_send.append(maintain(st, step, peer, "holds"))
                    post_send.append(maintain(st, step, peer, "joined"))
                    post_send.append(maintain(st, step, peer, "left"))
                    post_send.append(update_joined_before(st, step, peer))
                    post_send.append(update_left_after_joined(st, step, peer))
                event_list.append(And(pre_send,And(post_send)))
            

            # join(p1) event
            exists_joined_cond = []
            for peer in range(num_peers):
                exists_joined_cond.append(st[step][peer]["joined"])
            pre_join = And(Not(st[step][p1]["joined"]),
                           Not(st[step][p1]["left"]),
                           Or(exists_joined_cond))
            preconditions.append(pre_join)
            post_join = []
            for peer in range(num_peers):
                if peer == p1:
                    post_join.append(st[step + 1][peer]["joined"])
                else:
                    post_join.append(maintain(st, step, peer, "joined"))
                post_join.append(maintain(st, step, peer, "left"))
                post_join.append(maintain(st, step, peer, "holds"))
                post_join.append(maintain(st, step, peer, "has_sent"))
                post_join.append(update_joined_before(st, step, peer))
                post_join.append(update_left_after_joined(st, step, peer))
            event_list.append(And(pre_join,And(post_join)))

            # leave(p1) event
            all_sat_cond = []
            for peer in range(num_peers):
                all_sat_cond.append(Implies(st[step][peer]["joined"], 
                                            And(st[step][peer]["holds"], Not(st[step][peer]["has_sent"]))))
            pre_leave = And(st[step][p1]["joined"],
                            Not(st[step][p1]["left"]),
                            Or(st[step][p1]["has_sent"], And(all_sat_cond)))
            preconditions.append(pre_leave)
            post_leave = []
            for peer in range(num_peers):
                if peer == p1:
                    post_leave.append(st[step + 1][peer]["left"])
                    post_leave.append(Not(st[step + 1][peer]["joined"]))
                else:
                    post_leave.append(maintain(st, step, peer, "joined"))
                    post_leave.append(maintain(st, step, peer, "left"))
                post_leave.append(maintain(st, step, peer, "holds"))
                post_leave.append(maintain(st, step, peer, "has_sent"))
                post_leave.append(update_joined_before(st, step, peer))
                post_leave.append(update_left_after_joined(st, step, peer))
            event_list.append(And(pre_leave,And(post_leave)))


        # stutter event
        pre_stutter = Not(Or(preconditions))
        post_stutter = []
        for peer in range(num_peers):
            post_stutter.append(maintain(st, step, peer, "joined"))
            post_stutter.append(maintain(st, step, peer, "left"))
            post_stutter.append(maintain(st, step, peer, "holds"))
            post_stutter.append(maintain(st, step, peer, "has_sent"))
            post_stutter.append(update_joined_before(st, step, peer))
            post_stutter.append(update_left_after_joined(st, step, peer))
        event_list.append(And(pre_stutter, And(post_stutter)))
        s.add(Or(event_list))                

        # Invariants

        exists_joined_cond = []
        exists_holds_cond = []
        for peer in range(num_peers):
            s.add(Not(And(st[step+1][peer]["joined"],st[step+1][peer]["left"])))
            s.add(Implies(st[step+1][peer]["left"], st[step+1][peer]["holds"]))
            exists_joined_cond.append(st[step+1][peer]["joined"])
            exists_holds_cond.append(And(st[step+1][peer]["joined"], st[step+1][peer]["holds"]))
        s.add(Implies(Or(exists_joined_cond), Or(exists_holds_cond)))

    liveness_conds = []
    for peer in range(num_peers):
        liveness_conds.append(Implies(st[num_steps - 1][peer]["joined_before"], st[num_steps - 1][peer]["left_after_joined"]))
    
    # Check if liveness is violated!
    s.add(Not(And(liveness_conds)))

    res = s.check()


    print(res)
    if s.check() == sat:
        m = s.model()
        for peer in range(num_peers):
            for step in range(2):
                for k, v in st[step][peer].items():
                    print("peer {}, {} = {} at step {}".format(peer,k,m.evaluate(v), step))



if __name__ == '__main__':
    main(int(sys.argv[1]))