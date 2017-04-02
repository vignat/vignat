library(plyr)
library(ggplot2)

load_exp_data <- function(sources) {
  exp_data <- data.frame(V1=integer(), V2=integer(), medium=character())
  for (s in sources) {
    exp_data_i <- read.table(s[1])
    exp_data_i["medium"] <- s[2]
    exp_data <- rbind(exp_data, exp_data_i)
  }
  data.frame(abscissa=exp_data$V1, ordinata=exp_data$V2, medium=exp_data$medium)
}

plot_exp_data <- function(exp_data, titles) {
  pd <- position_dodge(0.01)
  summary=ddply(exp_data, c("abscissa", "medium"), summarise,
                N=length(ordinata), mean=mean(ordinata), sd=sd(ordinata))
  csummary=ddply(exp_data, c("medium", "abscissa", "ordinata"), nrow)
  ggplot(summary, aes(x=abscissa, y=mean,
                      colour=medium, group=medium)) +
      geom_errorbar(aes(ymin=mean-sd, ymax=mean+sd),
                    width=.03, position=pd, colour="black") +
      geom_line(position=pd) +
      geom_point(position=pd,size=3) +
      scale_x_continuous(trans='log10') +
      labs(title=titles$title) +
      xlab(titles$abscissa) +
      ylab(titles$ordinata) +
      geom_point(data=csummary,
                aes(x=abscissa, y=ordinata, colour=medium,
                    group=medium, size=V1),
                position=pd,
                show.legend=FALSE) +
      scale_size(range=c(0,2),trans="log",labels=NULL)
}
