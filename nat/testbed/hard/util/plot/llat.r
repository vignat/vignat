library(plyr)
library(ggplot2)
library(scales)
library(grid)

all_data <- data.frame(V1=integer(), V2=integer(),
                       V3=integer(), V4=integer(),
                       V5=integer(), V6=integer(),
                       middlebox=character())

vignat <- read.table("vignat-latency-breakpoint.txt")
vignat["middlebox"] <- "vignat"
unverified <- read.table("unverified-latency-breakpoint.txt")
unverified["middlebox"] <- "unverified"

all_data <- rbind(all_data, vignat)
all_data <- rbind(all_data, unverified)

cbbPalette <- c("#000000", "#E69F00", "#56B4E9", "#009E73", "#F0E442", "#0072B2", "#D55E00", "#CC79A7")

pd <- position_dodge(1)

p1 <- ggplot(all_data, aes(x=V3/1e6, y=V5/1e3,
                          group=middlebox,
                          color=middlebox,
                          shape=middlebox)) +
     geom_point(size=3) +
     geom_line() +
     geom_errorbar(aes(ymin=(V5-V6)/1e3, ymax=(V5+V6)/1e3), width=.01) +
     labs(title="1 way latency, single flow") +
     xlab("rate (Mpkt/s)") +
     ylab(bquote("1-way latency, microsec, log scale")) +
     theme_bw() +
     scale_y_log10(breaks = trans_breaks("log10", function(x) 10^x),
                   labels = trans_format("log10", math_format(10^.x))) +
     #expand_limits(x=0,y=0) +
     theme( plot.margin = unit( c(0,0,0,0) , "in" ) )

p2 <- ggplot(all_data, aes(x=V3/1e6, y=V4,
                          group=middlebox,
                          color=middlebox,
                          shape=middlebox)) +
     geom_point(size=3) +
     geom_line() +
     xlab("rate (Mpkt/s)") +
     ylab(bquote("packet loss, fraction, log scale")) +
     scale_y_log10(breaks = trans_breaks("log10", function(x) 10^x),
                   labels = trans_format("log10", math_format(10^.x))) +
     theme_bw() +
     #expand_limits(x=0,y=0) +
     theme( plot.margin = unit( c(0,0,0,0) , "in" ) )


png("lll.png",width=1700,height=1200,res=140)
grid.newpage()
grid.draw(rbind(ggplotGrob(p1), ggplotGrob(p2), size="last"))
dev.off()

#ggsave(filename="lll.png", plot=p)
#ggsave(filename="lll.png")
#print(p)