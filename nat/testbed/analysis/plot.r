library(plyr)
library(ggplot2)

load_missrates <- function(sources) {
  missrates <- data.frame(V1=integer(), V2=integer(), medium=character())
  for (s in sources) {
    missrates_i <- read.table(paste(s[1], ".dat", sep=""))
    missrates_i["medium"] <- s[2]
    missrates <- rbind(missrates, missrates_i)
  }
  data.frame(rate=1e6/missrates$V1, loss=missrates$V2, medium=missrates$medium)
}

plot_missrates <- function(missrates, fname) {
  pd <- position_dodge(0.01)
  summary=ddply(missrates, c("rate", "medium"), summarise,
                N=length(loss), mean=mean(loss), sd=sd(loss))
  csummary=ddply(missrates, c("medium", "rate", "loss"), nrow)
  ggplot(summary, aes(x=rate, y=mean,
                      colour=medium, group=medium)) +
      geom_errorbar(aes(ymin=mean-sd, ymax=mean+sd),
                    width=.03, position=pd, colour="black") +
      geom_line(position=pd) +
      geom_point(position=pd,size=3) +
      scale_x_continuous(trans='log10') +
      labs(title="Comparative loss/rate dependencies for [tester]-[medium]-[reflector] scenarios") +
      xlab("Source packet rate, packets/second, log scale") +
      ylab("Packet loss (sent pkts - received pkts)/sent pkts, %") +
      geom_point(data=csummary,
                aes(x=rate, y=loss, colour=medium,
                    group=medium, size=V1),
                position=pd,
                show.legend=FALSE) +
      scale_size(range=c(0,2),trans="log",labels=NULL)
}
