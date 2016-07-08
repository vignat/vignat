library(plyr)
library(ggplot2)

missrates_nat = read.table("mynat.dat")
missrates_nat["medium"] <- "nat"
missrates_router = read.table("router.dat")
missrates_router["medium"] <- "router"
missrates_direct = read.table("direct.dat")
missrates_direct["medium"] <- "direct"
missrates_netfilter= read.table("netfilter.dat")
missrates_netfilter["medium"] <- "netfilter"
missrates <- rbind(missrates_nat, missrates_router, missrates_direct, missrates_netfilter)
pd <- position_dodge(0.01)
#summary_nat=ddply(missrates_nat, "V1", summarise, N=length(V2), mean=mean(V2), sd=sd(V2))
#summary_router=ddply(missrates_router, "V1", summarise, N=length(V2), mean=mean(V2), sd=sd(V2))
summary=ddply(missrates, c("V1", "medium"), summarise, N=length(V2), mean=mean(V2), sd=sd(V2))
comp_deps <-
  ggplot(summary, aes(x=1e6/V1, y=mean, colour=medium, group=medium)) +
      geom_errorbar(aes(ymin=mean-sd, ymax=mean+sd),
                    width=.03, position=pd, colour="black") +
      geom_line(position=pd) +
      geom_point(position=pd,size=3) +
      scale_x_continuous(trans='log10') +
      labs(title="Comparative loss/rate dependencies") +
      xlab("Rate, packets/second") +
      ylab("Loss, %")

ggsave(filename="plot.pdf", plot=comp_deps)
