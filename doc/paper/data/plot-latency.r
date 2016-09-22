
library(plyr)
library(ggplot2)

load_exp_data <- function(sources) {
  exp_data <- data.frame(V1=integer(), V2=integer(), middlebox=character())
  for (s in sources) {
    exp_data_i <- read.table(s[1])
    exp_data_i["middlebox"] <- s[2]
    exp_data <- rbind(exp_data, exp_data_i)
  }
  ## 2 here stands for the 2 bounces netperf does for each request in RTT
  data.frame(abscissa=exp_data$V1/1000, ordinata=1000000/2/exp_data$V2, middlebox=exp_data$middlebox)
}

plot_exp_data <- function(exp_data, titles) {
  cbbPalette <- c("#000000", "#E69F00", "#56B4E9", "#009E73", "#F0E442", "#0072B2", "#D55E00", "#CC79A7")

  labs <- c(bquote("VigNAT" * alpha), bquote("VigNAT" * beta), "LinuxNAT", "Plain forwarding")
  brks <- c("VigNAT unopt", "VigNAT", "NF-NAT", "Plain fwding")

  #exp_data <- exp_data[exp_data$abscissa != 10,]
  ggplot(exp_data, aes(x=abscissa, y=ordinata,
                       group=middlebox, color=middlebox,
                       shape=middlebox,
                       linetype=middlebox)) +
      scale_color_manual(labels=labs, breaks=brks, 
                         values=c("NF-NAT" = "#000000",
                                  "VigNAT unopt" = "#E69F00",
                                  "VigNAT" = "#56B4E9",
                                  "Plain fwding" = "#D55E00")) +
      scale_shape_manual(labels=labs, breaks=brks,
                         values=c("NF-NAT" = 15,
                                  "VigNAT unopt" =19,
                                  "VigNAT" = 17,
                                  "Plain fwding" = 5)) +
      scale_linetype_manual(labels=labs, breaks=brks,
                            values=c("NF-NAT" = 1,
                                     "VigNAT unopt" =1,
                                     "VigNAT" = 1,
                                     "Plain fwding" = 2)) +
      #geom_smooth(method='lm', size=2, formula=y~poly(x,1), se=FALSE) +
      geom_point(size=4) +
      geom_smooth(se=FALSE, span=0.5, size=2) +
      coord_cartesian(ylim=c(80, 150)) +
      theme_bw() +
      #expand_limits(x=0, y=0) +
      labs(title=titles$title) +
      xlab(titles$abscissa) +
      ylab(expression("One-way latency," ~ mu *"s")) +
      theme(aspect.ratio=0.6,
            legend.text=element_text(size=19),
            legend.background = element_rect(fill="transparent"),
            legend.position=c(0.3, 0.75),
            text=element_text(size=19)) +
      guides(color=guide_legend(title=titles$legend,
                                keywidth=0.3,
                                keyheight=0.3,
                                default.unit="inch")) +
      guides(linetype=guide_legend(title=titles$legend,
                                keywidth=0.3,
                                keyheight=0.3,
                                default.unit="inch")) +
      guides(shape=guide_legend(title=titles$legend,
                                keywidth=0.3,
                                keyheight=0.3,
                                default.unit="inch"))
}

exp_data <- load_exp_data(list(c("latency/vig-nat.txt", "VigNAT unopt"),
                               c("latency/vig-nat2.txt", "VigNAT unopt"),
                               c("latency/vig-nat3.txt", "VigNAT unopt"),
                               c("latency/nf-nat.txt", "NF-NAT"),
                               #c("latency/many-flows/nf-nat.txt", "NF-NAT"),
                               c("latency/lat-res-stub.txh", "Plain fwding"),
                               c("latency/vig-nat-opt.txt", "VigNAT"),
                               #c("latency/many-flows/vig-nat-opt.txt", "VigNAT"),
                               c("latency/vig-nat-opt3.txt", "VigNAT")
                       ))

exp_data <- exp_data[exp_data$ordinata < 1000,]
exp_data <- exp_data[!(exp_data$abscissa > 25 & exp_data$middlebox == "VigNAT unopt"), ]

comp_deps <-
  plot_exp_data( exp_data,
                 data.frame(title="",
                            #title="Comparative latency for differen number of concurrent connectoin on 1Gbps link",
                             abscissa="Number of concurrent flows, thousands",
                             ordinata="///set directly in the plot///",
                             legend=""))

ggsave(filename="lat.pdf", plot=comp_deps, width=7, height=4.5)