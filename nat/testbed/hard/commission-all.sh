scp client-commission.sh icnalsp3s1.epfl.ch:client-commission.sh
scp client-provision.sh icnalsp3s1.epfl.ch:client-provision.sh
ssh icnalsp3s1.epfl.ch 'sh ~/client-commission.sh'

scp nat-commission.sh icnalsp3s2.epfl.ch:nat-commission.sh
scp nf-nat.sh icnalsp3s2.epfl.ch:nf-nat.sh
ssh icnalsp3s2.epfl.ch 'sh ~/nat-commission.sh'

scp server-commission.sh icnalsp3s3.epfl.ch:server-commission.sh
scp server-provision.sh icnalsp3s3.epfl.ch:server-provision.sh
ssh icnalsp3s3.epfl.ch 'sh ~/server-commission.sh'

# the network:
# client{icnalsp3s1}[em3] 192.168.3.5 -- 192.168.3.2 [em3]nat{icnalsp3s2}
# nat{icnalsp3s2}[em2] 192.168.2.2 -- 192.168.2.10 [em2]server{icnalsp3s3}
# server{icnalsp3s3}[em3] 192.168.0.10 -- 192.168.0.5 [em2]client{icnalsp3s1}
