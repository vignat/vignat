
library(plyr)
library(ggplot2)

test_duration <- 40

load_exp_data <- function(sources) {
  exp_data <- data.frame(V1=integer(), V2=integer(),
                         V3=integer(), V4=integer(),
                         middlebox=character())
  for (s in sources) {
    exp_data_i <- read.table(s[1])
    exp_data_i["middlebox"] <- s[2]
    exp_data <- rbind(exp_data, exp_data_i)
  }
  ## 2 here stands for the 2 bounces netperf does for each request in RTT
  data.frame(abscissa=exp_data$V1/1000, ordinata=exp_data$V4/test_duration/1e6, middlebox=exp_data$middlebox)
}

plot_exp_data <- function(exp_data, titles) {
  cbbPalette <- c("#000000", "#E69F00", "#56B4E9", "#009E73", "#F0E442", "#0072B2", "#D55E00", "#CC79A7")

  labs <- c(bquote("VigNAT" * alpha), bquote("VigNAT" * beta), "LinuxNAT", "Plain forwarding")
  brks <- c("VigNAT unopt", "VigNAT", "NF-NAT", "Plain fwding")

  exp_data <- exp_data[exp_data$abscissa != 10,]
  ggplot(exp_data, aes(x=abscissa, y=ordinata,
                       group=middlebox, color=middlebox,
                       shape=middlebox)) +
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
      geom_point(size=4) +
      theme_bw() +
      geom_line(size=2) +
      labs(title=titles$title) +
      xlab(titles$abscissa) +
      ylab(titles$ordinata) +
      theme(aspect.ratio=0.6,
            legend.text=element_text(size=19),
            legend.background = element_rect(fill="transparent"),
            legend.position=c(0.2, 0.6),
            text=element_text(size=19)) +
      guides(color=guide_legend(title=titles$legend,
                                keywidth=0.3,
                                keyheight=0.3,
                                default.unit="inch")) +
      guides(shape=guide_legend(title=titles$legend,
                                keywidth=0.3,
                                keyheight=0.3,
                                default.unit="inch"))
}

exp_data <- load_exp_data(list(c("throughput-break/vig-nat-rt.txt", "VigNAT unopt"),
                               c("throughput-break/tight/vig-nat-rt.txt", "VigNAT unopt"),
                               c("throughput-break/low/vig-nat-rt.txt", "VigNAT unopt"),
                               c("throughput-break/more-detail/vig-nat-rt.txt", "VigNAT unopt"),
                               c("throughput-break/nf-nat-rt.txt", "NF-NAT"),
                               c("throughput-break/tight/nf-nat-rt.txt", "NF-NAT"),
                               c("throughput-break/more-detail/nf-nat-rt.txt", "NF-NAT"),
                               c("throughput-break/low/nf-nat-rt.txt", "NF-NAT"),
                               c("throughput-break/vig-opt-nat-rt.txt", "VigNAT"),
                               c("throughput-break/more-detail/vig-opt-nat-rt.txt", "VigNAT"),
                               c("throughput-break/tight/vig-opt-nat-rt.txt", "VigNAT"),
                               c("throughput-break/low/vig-opt-nat-rt.txt", "VigNAT")
                       ))

exp_data <- exp_data[exp_data$absciss != 30, ]

comp_deps <-
  plot_exp_data( exp_data,
                 data.frame(title="",#title="The maximum packet rate for the given number of flows with 1%loss",
                             abscissa="Number of concurrent flows, thousands",
                             ordinata="Throughput, Mpkt/s",
                             legend=""))

ggsave(filename="brpt.pdf", plot=comp_deps, width=7, height=4.5)