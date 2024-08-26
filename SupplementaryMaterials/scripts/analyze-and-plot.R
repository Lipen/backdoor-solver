library(tidyverse)
library(cowplot)
library(ggsci)

######################################

## Change to your directory:
# setwd("~/dev/backdoor-solver/SupplementaryMaterials")

## Prevent generation of 'Rplots.pdf' when using Rscript:
if(!interactive()) pdf(NULL)

######################################

raw <- read_csv("data/results-satcomp.csv")

df.wide <- raw |>
    pivot_longer(!instance, names_to = "solver", values_to = "time") |>
    mutate(time = ifelse(time > 5000, 10000, time)) |>
    pivot_wider(names_from = solver, values_from = time) |>
    rowwise() |>
    mutate(VBSint = min(int118, int120, int121, int126)) |>
    mutate(VBS = min(cad195, VBSint)) |>
    ungroup()
df.wide

df.long <- df.wide |>
    pivot_longer(!instance, names_to = "solver", values_to = "time") |>
    group_by(solver) |>
    arrange(time) |>
    mutate(index = row_number()) |>
    ungroup()
df.long

stats.solved <- df.long |>
    group_by(solver) |>
    summarize(solved = sum(time <= 5000), .groups = "drop") |>
    arrange(desc(solved))
stats.solved


## mkdir -p out
dir.create("out", showWarnings = FALSE, recursive = TRUE)


### CACTUS

p.cactus <- df.long |>
    mutate(s = case_match(solver,
        "cad195" ~ paste0("CaDiCaL 1.9.5 (", stats.solved$solved[stats.solved$solver == "cad195"], "/116)"),
        "int118" ~ paste0("Interleave-118 (", stats.solved$solved[stats.solved$solver == "int118"], "/116)"),
        "int120" ~ paste0("Interleave-120 (", stats.solved$solved[stats.solved$solver == "int120"], "/116)"),
        "int121" ~ paste0("Interleave-121 (", stats.solved$solved[stats.solved$solver == "int121"], "/116)"),
        "int126" ~ paste0("Interleave-126 (", stats.solved$solved[stats.solved$solver == "int126"], "/116)"),
        "VBS"    ~ paste0("VBS (", stats.solved$solved[stats.solved$solver == "VBS"], "/116)"),
        "VBSint" ~ paste0("VBS-Interleave (", stats.solved$solved[stats.solved$solver == "VBSint"], "/116)"),
    )) |>
    mutate(s = fct_rev(fct_reorder(s, solver, function(s) {
        # print(s)
        stats.solved$solved[stats.solved$solver == first(s)]
    }))) |>
    ggplot(aes(x = index, y = time)) +
    geom_hline(yintercept = 5000, color = "darkgray", linetype = "dashed", linewidth = 0.5) +
    geom_line(aes(color = s), linewidth = 0.3) +
    geom_point(aes(color = s, shape = s), size = 1) +
    coord_cartesian(ylim = c(NA,5000)) +
    scale_shape_manual(values = c(1,2,4,5,6,7,8)) +
    scale_color_bmj() +
    labs(x = "Instances solved",
         y = "Time (s)",
         color = NULL,
         shape = NULL) +
    theme_bw() +
    theme(
        legend.position = "inside",
        legend.justification.inside = c(0.99,0.02),
        legend.key.size = unit(0.8, "lines"),
        text = element_text(size = 8),
    )
p.cactus

ggsave("out/plot_cactus_on116.pdf", plot = p.cactus,
       width = 7.05, height = 2.8, units = "in")


### SCATTER
my.red <- "red2"

p.scatter.int120 <- df.wide |>
    select(instance, cad195, int120) |>
    mutate(timeout = cad195 > 5000 | int120 > 5000) |>
    pivot_longer(!c(instance, timeout), names_to = "solver", values_to = "time") |>
    mutate(time = ifelse(time > 5000, 5000, time)) |>
    mutate(time = ifelse(time < 1, 1, time)) |>
    pivot_wider(names_from = solver, values_from = time) |>
    ggplot(aes(x = cad195, y = int120)) +
    geom_hline(yintercept = 5000, color = my.red, linetype = "dashed", linewidth = 0.3) +
    geom_vline(xintercept = 5000, color = my.red, linetype = "dashed", linewidth = 0.3) +
    geom_abline(slope = 1, intercept = 0, color = my.red, linetype = "dashed", linewidth = 0.3) +
    geom_point(aes(color = timeout), size = 0.3) +
    scale_color_manual(values = c("black", my.red), guide = guide_none()) +
    coord_fixed(xlim = c(1, 5000), ylim = c(1, 5000)) +
    labs(
        x = "Baseline time (CaDiCaL 1.9.5), s",
        y = "Time interleave-120, s",
        color = "Timeout",
    ) +
    theme_bw() +
    theme(
        text = element_text(size = 6),
    )
p.scatter.int120

p.scatter.vbsint <- df.wide |>
    select(instance, cad195, VBSint) |>
    mutate(timeout = cad195 > 5000 | VBSint > 5000) |>
    pivot_longer(!c(instance, timeout), names_to = "solver", values_to = "time") |>
    mutate(time = ifelse(time > 5000, 5000, time)) |>
    mutate(time = ifelse(time < 1, 1, time)) |>
    pivot_wider(names_from = solver, values_from = time) |>
    ggplot(aes(x = cad195, y = VBSint)) +
    geom_hline(yintercept = 5000, color = my.red, linetype = "dashed", linewidth = 0.3) +
    geom_vline(xintercept = 5000, color = my.red, linetype = "dashed", linewidth = 0.3) +
    geom_abline(slope = 1, intercept = 0, color = my.red, linetype = "dashed", linewidth = 0.3) +
    geom_point(aes(color = timeout), size = 0.3) +
    scale_color_manual(values = c("black", my.red), guide = guide_none()) +
    coord_fixed(xlim = c(1, 5000), ylim = c(1, 5000)) +
    labs(
        x = "Baseline time (CaDiCaL 1.9.5), s",
        y = "Time VBS-Interleave, s",
        color = "Timeout",
    ) +
    theme_bw() +
    theme(
        text = element_text(size = 6),
    )
p.scatter.vbsint


plot_grid(
    p.scatter.int120,
    p.scatter.vbsint,
    nrow = 1
)
ggsave("out/plot_scatters_on116.pdf",
       width = 3.4, height = 1.6, units = "in")
