
vagrant ssh -c 'bash /vagrant/redeploy-nat.sh 10 1' nat
vagrant ssh -c 'bash /vagrant/hpingtst.sh' client
vagrant ssh -c 'cp result.txt /vagrant/resk1.dat' client

vagrant ssh -c 'bash /vagrant/redeploy-nat.sh 10 1024' nat
vagrant ssh -c 'bash /vagrant/hpingtst.sh' client
vagrant ssh -c 'cp result.txt /vagrant/resk1024.dat' client

vagrant ssh -c 'bash /vagrant/redeploy-nat.sh 10 60000' nat
vagrant ssh -c 'bash /vagrant/hpingtst.sh' client
vagrant ssh -c 'cp result.txt /vagrant/resk160k.dat' client
