library(plyr)
library(ggplot2)

missrates_nat = read.table("mynat.dat")
missrates_nat["src"] <- "nat"
missrates_router = read.table("router.dat")
missrates_router["src"] <- "router"
missrates_direct = read.table("direct.dat")
missrates_direct["src"] <- "direct"
missrates <- rbind(missrates_nat, missrates_router, missrates_direct)
pd <- position_dodge(0.01)
#summary_nat=ddply(missrates_nat, "V1", summarise, N=length(V2), mean=mean(V2), sd=sd(V2))
#summary_router=ddply(missrates_router, "V1", summarise, N=length(V2), mean=mean(V2), sd=sd(V2))
summary=ddply(missrates, c("V1", "src"), summarise, N=length(V2), mean=mean(V2), sd=sd(V2))
ggplot(summary, aes(x=1000/V1, y=mean, colour=src, group=src)) +
  geom_errorbar(aes(ymin=mean-sd, ymax=mean+sd),
                width=.03, position=pd, colour="black") +
  geom_line(position=pd) +
  geom_point(position=pd,size=3) +
  scale_x_continuous(trans='log10')
