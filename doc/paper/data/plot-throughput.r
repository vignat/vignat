
library(plyr)
library(ggplot2)

load_exp_data <- function(sources) {
  exp_data <- data.frame(V1=integer(),
                         V2=integer(),
                         V3=integer(),
                         V4=integer(),
                         V5=integer(),
                         V6=integer(),
                         middlebox=character())
  for (s in sources) {
    exp_data_i <- read.table(s[1])
    exp_data_i["middlebox"] <- s[2]
    exp_data <- rbind(exp_data, exp_data_i)
  }
  data.frame(abscissa=exp_data$V4/exp_data$V6/1e6*1e3, ordinata=exp_data$V5/exp_data$V6/1e6*1e3, middlebox=exp_data$middlebox, pktsize=exp_data$V2, nflows=exp_data$V1)
}

plot_exp_data <- function(exp_data, titles) {
  cbbPalette <- c("#000000", "#E69F00", "#56B4E9", "#009E73", "#F0E442", "#0072B2", "#D55E00", "#CC79A7")

  labs <- c(bquote("VigNAT" * alpha), bquote("VigNAT" * beta), "LinuxNAT")
  brks <- c("VigNAT unopt", "VigNAT", "NF-NAT")

  exp_data <- exp_data[exp_data$pktsize==64,]
  exp_data <- exp_data[order(exp_data$abscissa,exp_data$pktsize),]
  exp_data <- exp_data[order(exp_data$abscissa,exp_data$pktsize),]
  ggplot(exp_data, aes(x=abscissa, y=ordinata, group=middlebox,
                       color=middlebox, shape=middlebox)) +
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
      geom_segment(aes(x=0,y=0,xend=1.6,yend=1.6),color=c('light gray')) +
      geom_line(size=2) +
      geom_point(size=4) +
      theme_bw() +
      labs(title=titles$title) +
      xlab(titles$abscissa) +
      ylab(titles$ordinata) +
      theme(aspect.ratio=1,
            legend.text=element_text(size=19),
            legend.background = element_rect(fill="transparent"),
            legend.position=c(0.3, 0.8),
            text=element_text(size=19)) +
      coord_fixed() +
      guides(color=guide_legend(title=titles$legend,
                                keywidth=0.3,
                                keyheight=0.3,
                                default.unit="inch")) +
      guides(shape=guide_legend(title=titles$legend,
                                keywidth=0.3,
                                keyheight=0.3,
                                default.unit="inch"))
}

exp_data <- 
    load_exp_data(list(c("throughput/nf-nat-rt.txt", "NF-NAT"),
                       c("throughput/50k59k/nf-nat-rt.txt", "NF-NAT"),
                       c("throughput/detailed/nf-nat-rt.txt", "NF-NAT"),
                       c("throughput/27900/nf-nat-rt.txt", "NF-NAT"),
                       c("throughput/vig-nat-rt.txt", "VigNAT unopt"),
                       c("throughput/detailed/vig-nat-rt.txt", "VigNAT unopt"),
                       c("throughput/50k59k/vig-nat-rt.txt", "VigNAT unopt"),
                       c("throughput/27900/vig-nat-rt.txt", "VigNAT unopt"),
                       c("throughput/vig-opt-nat-rt.txt", "VigNAT"),
                       c("throughput/detailed/vig-opt-nat-rt.txt", "VigNAT"),
                       c("throughput/50k59k/vig-opt-nat-rt.txt", "VigNAT"),
                       c("throughput/27900/vig-opt-nat-rt.txt", "VigNAT")
    ))

comp_deps27900 <-
  plot_exp_data( exp_data[exp_data$nflows == 27900,],
                        data.frame(title="",#title="Send/Receive for 50K concurrent flows on 1Gbps link",
                             abscissa="Send packet rate, Mpkt/s",
                             ordinata="Receive packet rate, Mpkt/s",
                             legend=""))

comp_deps59k <-
  plot_exp_data( exp_data[exp_data$nflows == 59000,],
                        data.frame(title="",#title="Send/Receive for 59K concurrent flows on 1Gbps link",
                             abscissa="Send packet rate, Mpkt/s",
                             ordinata="Receive packet rate, Mpkt/s",
                             legend=""))

ggsave(filename="rt27900.pdf", plot=comp_deps27900)
ggsave(filename="rt59k.pdf", plot=comp_deps59k)