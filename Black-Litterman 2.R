library(PerformanceAnalytics)
library(zoo)
library(tseries)
library(fAssets)
library(fPortfolio)
library(tidyquant) # To download the data
library(plotly) # To create interactive charts
library(timetk) # To manipulate the data series
library(plotly)
library(ggplot2)
library(data.table)
library(scales)
library(ggcorrplot)
library(RiskPortfolios)
library(quantmod)
library(PeerPerformance)

setwd("~/Desktop/Speciale")


return <- read.csv2("Md data.csv", header= TRUE, sep = ';' )

#prices <- merge(oli_price,prices, by='date')


return2  <- return[, c("Danske.Aktier", "Globale.Aktier", "StabileAktier", "Emerging.market", "Indeksobligationer", 
                       'Statsobligationer', 'Realkredit', 'IGObligationer', 'HYObligationer', 
                       'EMDHARD', 'EMDLocal', 'PE', 'Infrastructure', 'Skov', 'RealEstate', 'riskfree', "MSCI.World.Index", 'oli_price', 'term', 'spread', 'premium', 'production', 'Inflation' ), drop = F]

colnames(return2) <- c( "Danske.Aktier", "Globale.Aktier", "StabileAktier", "Emerging.market", "Indeksobligationer", 
                        'Statsobligationer', 'Realkredit', 'IGObligationer', 'HYObligationer', 
                        'EMDHARD', 'EMDLocal', 'PE', 'Infrastructure', 'Skov', 'RealEstate', 'riskfree', "MSCI.World.Index", 'oli_price', 'term', 'spread', 'premium', 'production', 'Inflation' )


rownames(return2) <- return$date
as.matrix(return2)
return2$riskfree <- (return2$riskfree)/12

#Substracting the riskfree rate and reducing the data set:
returns.mat = coredata(return2)
exReturns.mat = returns.mat[1:15]
exReturns.mat = exReturns.mat - return2$riskfree
exReturns.df = as.data.frame(exReturns.mat)



################Construction of Pf3, Pf4, Pf5 ##################

#Market weights:
#Pf3: 
w_lp <- c(0.059, 0.193, 0.15, 0.105, 0.01, 0.065, 0.233, 0.05, 0.03, 0.04, 0.075, 0.025, 0.03, 0.025, 0.055)
w_lp <- w_lp/sum(w_lp)
round(w_lp*100,3)

#Pf4
w_eq <- c(rep(1/15, 15))

#Pf5
w_mkt <- c(0.35979, 36.26150, 13.34417, 12.47163, 0.00001, 0.00303, 0.00030, 0.95249, 0.19211, 0.00007, 0.00012, 33.74943, 2.36841, 0.09705, 0.19990)/100


# Shrinkage covariance matrix
PriorCov <- function(periode){
  
  begin <- periode 
  end <- 119 + periode
  
  # Shrinkage of the covariance matrix towards constant correlation matrix by Ledoit-Wolf
  cov_mat<-covEstimation(as.matrix(exReturns.df[begin:end,1:15]), control = list(type = 'cor'))
  
  return(cov_mat)
}

#Derive equilibrium return vector Pi:
Pi.fun = function(cov, weights.vector, lambda ){
  return(lambda* cov %*% (weights.vector))
}


#Views expected rates of return vector Q:
Q_foecast = function(periode){
  
  Q = forcast[periode,]*100
  Q <- as.numeric(Q)
  return(Q)
  
}

#The uncertainty of the views Omega:
Omega_foecast = function(periode){
  
  Omega <- matrix( c(rep(0,15)), nrow = 15, ncol = 15)
  for (i in 1:15) {
    Omega[i,i] <- forecastsigma[periode,i]*100
  }
  
  return(Omega)
  
}


# Black-Litterman vector of mean return mu_BL::
mu_BL=function(Q,P,Tau,Omega,Pi.posterior,cov.matrix){
  
  return(solve((solve(Tau*cov.matrix)+t(P)%*%solve(Omega)%*%P))%*%(solve(Tau*cov.matrix)%*%Pi.posterior+t(P)%*%solve(Omega)%*%Q))
}

# Black-Litterman covariance matrix Sigma_BL
Sigma_BL=function(P,Tau,Omega,cov.matrix){
  
  return((1+Tau)*cov.matrix - (Tau^2) * cov.matrix %*% t(P) %*% solve(Tau * P %*% cov.matrix %*% t(P) + Omega) %*% P %*% cov.matrix)
}

#Markowitz portfolio optimization with no short and budget constrain:: 
portolioMarkowitz <- function(lambda, mu, Sigma) {
  w <- Variable(nrow(Sigma))
  prob <- Problem(Maximize(t(mu) %*% w - lambda*quad_form(w, Sigma)),
                  constraints = list( w >= 0, sum(w) == 1))
  result <- solve(prob)
  return(as.vector(result$getValue(w)))
}

#Pick matrix with absolute views:
P <- matrix( c(rep(0,15)), nrow = 15, ncol = 15)
for (i in 1:15) {
  P[i,i] <- 1
}

#Creating optimal Black-Litterman weight:
BL_optimal_weights = function(periode, weight, Tau, lambda){
  
  #Equlibrium return
  priorCov <- PriorCov(periode)
  Pi=Pi.fun(priorCov, weight, lambda)
  
  #Views
  Q <- Q_foecast(periode) #Expecttion to the future
  colnames(P)=colnames(priorCov) # PickMatrix
  Omega <- Omega_foecast(periode)
  
  #Black-Litterman return and variance
  return_BL=mu_BL(Q,P,Tau,Omega,Pi,priorCov)
  
  sigma_BL = Sigma_BL(P, Tau, Omega, priorCov)
  
  #Optimal weights
  optpf_BL<-round(portolioMarkowitz(lambda, return_BL, sigma_BL)*100,4)
  names(optpf_BL) <- colnames(priorCov)
  
  return(optpf_BL)
  
}

# Optimal weights for each period based on the chosen market portfolio:
opt_weight <- function(weight, Tau, lambda){
  
  weight_holdning <- matrix(0, nrow = 32, ncol = 15)
  colnames(weight_holdning) <- colnames(return2[,1:15])
  
  for (i in 1:32) {
    
    weight_holdning[i,] <- BL_optimal_weights(i, weight, Tau, lambda )
    
  }
  
  return(weight_holdning)
  
}

opt_lp <- opt_weight(w_lp, Tau = 0.01, lambda = 2.5) #Pf3
opt_mkt <- opt_weight(w_mkt, Tau = 0.01, lambda = 2.5) #Pf4
opt_eq <- opt_weight(w_eq, Tau = 0.01, lambda = 2.5) #Pf5

#Realized return Black-Litterman pf:
realised_return_lp <- c()
realised_return_mkt <- c()
realised_return_eq <- c()

for (i in 1:32) {
  
  tt <- i + 120 # One periode ahead compared to what has created the weights
  realised_return_lp[i] <- as.matrix(exReturns.df[tt,1:15]) %*% opt_lp[i,]/100
  realised_return_mkt[i] <- as.matrix(exReturns.df[tt,1:15]) %*% opt_mkt[i,]/100
  realised_return_eq[i] <- as.matrix(exReturns.df[tt,1:15]) %*% opt_eq[i,]/100
}


######################## Pf1 ########################

w_equal2  <- matrix(1/15, nrow = 32, ncol = 15)
colnames(w_equal2) <- colnames(opt_lp)

w_equal <- c(rep(1/15,15))

#Realized return Pf1
realised_return_equal <- c()
for (i in 1:32) {
  
  tt <- i + 120 # One periode ahead compared to what has created the weights
  realised_return_equal[i] <- as.matrix(exReturns.df[tt,1:15]) %*% as.vector(w_equal*100)
  
}
realised_return_equal


########################### Pf2 ################################: 
#Expected return
mu_mv <- function(periode){
  
  Start = periode
  End = periode + 119
  
  mu_mv2 <- colMeans(exReturns.df[Start:End, 1:15])
  return(mu_mv2)
  
}

#Shinkages covarnace matrix 
sigma_mv <- function(periode){
  
  Start = periode
  End = periode + 119
  
  sigma_mv2 <- covEstimation(as.matrix(exReturns.df[Start:End,1:15]), control = list(type = 'cor'))
  return(sigma_mv2)
  
}

portolioMarkowitz2 <- function(lambda, mu, Sigma) {
  w <- Variable(nrow(Sigma))
  prob <- Problem(Minimize(lambda*quad_form(w, Sigma)),
                  constraints = list(w >= 0, sum(w) == 1))
  result <- solve(prob)
  return(as.vector(result$getValue(w)))
}


# Weights mean variance Pf2: 

MV_optimal_weights <- function(periode,lambda = 2.5) {
  Mu_mv_a = mu_mv(periode)
  Sigma_mv_a = sigma_mv(periode)
  
  optpf_MV<-round(portolioMarkowitz(lambda = 2.5,Mu_mv_a, Sigma_mv_a)*100,4)
  return(optpf_MV)
}


#Optimal weigts Pf2 all times

weight_holdning_MV <- function(lambda){
  
  weight_holdning_MV <- matrix(0, nrow = 32, ncol = 15)
  colnames(weight_holdning_MV) <- colnames(return2[,1:15])
  for (i in 1:32) {
    
    weight_holdning_MV[i,] <- MV_optimal_weights(i, lambda)
    
  }
  return(weight_holdning_MV)
}

w_mv_shrinkage <- weight_holdning_MV(lambda = 2.5)

#Calculating the realized return for MV 
return_MV_shrinkage <- c()
for (i in 1:32) {
  
  tt <- i + 120 # One periode ahead compared to what has created the weights
  return_MV_shrinkage[i] <- as.matrix(exReturns.df[tt,1:15]) %*% w_mv_shrinkage[i,]
  
}

return_MV_shrinkage

################################# Performance measures ############################
names <- c('BL_LP', 'BL_mkt', 'BL_eq', 'w_eq', 'mv_shrikage')
number_of_pf <- 5
all_realized<-cbind(c(realised_return_lp*100), c(realised_return_mkt*100), c(realised_return_eq*100), c(realised_return_equal), c(return_MV_shrinkage))
colnames(all_realized) <- names

#Final return 
all_realized2<- as.data.frame(all_realized/100)
return_cum <- cumprod(1+all_realized2)
round((return_cum[32,]-1)*100,3)

#Average Return(%)
Average_return <- matrix(0, nrow = 1, ncol = number_of_pf)
colnames(Average_return) <- names
for (i in 1:number_of_pf) {
  
  nn <- names[i]
  
  Average_return[i] <- mean(all_realized[,nn])
  
}
Average_return


#Standard Deviation
Standard_Deviation <- matrix(0, nrow = 1, ncol = number_of_pf)
colnames(Standard_Deviation) <- names
for (i in 1:number_of_pf) {
  
  nn <- names[i]
  
  Standard_Deviation[i] <- sd(all_realized[,nn])
  
}
round(Standard_Deviation,3)

#Sharpe ratio
Sharp_ratio <- matrix(0, nrow = 1, ncol = number_of_pf)
colnames(Sharp_ratio) <- names
for (i in 1:number_of_pf) {
  
  Sharp_ratio[i] <- (Average_return[i] - mean(return2$riskfree[121:152])*100)/Standard_Deviation[i]
  
}

round(Sharp_ratio,3)

#Min
min_return <- matrix(0, nrow = 1, ncol = number_of_pf)
colnames(min_return) <- names
for (i in 1:number_of_pf) {
  
  nn <- names[i]
  
  min_return[i] <- min(all_realized[,nn])
  
}

round(min_return,3)

#Max
max_return <- matrix(0, nrow = 1, ncol = number_of_pf)
colnames(max_return) <- names
for (i in 1:number_of_pf) {
  
  nn <- names[i]
  
  max_return[i] <- max(all_realized[,nn])
  
}
round(max_return,3)



######## Turnover calculation

#The weights going from t to t+1
w_plus_BL_LP <- matrix(0, nrow = 32, ncol = 15)
w_plus_BL_mkt <- matrix(0, nrow = 32, ncol = 15)
w_plus_BL_eq <- matrix(0, nrow = 32, ncol = 15)
w_plus_w_eq <- matrix(0, nrow = 32, ncol = 15)
w_plus_mv_shrikage <- matrix(0, nrow = 32, ncol = 15)

colnames(w_plus_BL_LP) <- colnames(return2[,1:15])
colnames(w_plus_BL_mkt) <- colnames(return2[,1:15])
colnames(w_plus_BL_eq) <- colnames(return2[,1:15])
colnames(w_plus_w_eq) <- colnames(return2[,1:15])
colnames(w_plus_mv_shrikage) <- colnames(return2[,1:15])

for (i in 1:32) {
  tt <- i + 120 # One periode ahead compared to what has created the weights
  
  w_plus_BL_LP[i,] <- (opt_lp[i,] * (1 + as.matrix(exReturns.df[tt,1:15])))/ sum( opt_lp[i,] * (1 + as.matrix(exReturns.df[tt,1:15])))
  w_plus_BL_mkt[i,] <- (opt_mkt[i,] * (1 + as.matrix(exReturns.df[tt,1:15])))/ sum( opt_mkt[i,] * (1 + as.matrix(exReturns.df[tt,1:15])))
  w_plus_BL_eq[i,] <- (opt_eq[i,] * (1 + as.matrix(exReturns.df[tt,1:15])))/ sum( opt_eq[i,] * (1 + as.matrix(exReturns.df[tt,1:15])))
  w_plus_w_eq[i,] <- (w_equal2[i,] * (1 + as.matrix(exReturns.df[tt,1:15])))/ sum( w_equal2[i,] * (1 + as.matrix(exReturns.df[tt,1:15])))
  w_plus_mv_shrikage[i,] <- (w_mv_shrinkage[i,] * (1 + as.matrix(exReturns.df[tt,1:15])))/ sum( w_mv_shrinkage[i,] * (1 + as.matrix(exReturns.df[tt,1:15])))
  
}

turnover_mat_BL_LP <- matrix(0, nrow = 31, ncol = 15)
turnover_mat_BL_mkt <- matrix(0, nrow = 31, ncol = 15)
turnover_mat_BL_eq <- matrix(0, nrow = 31, ncol = 15)
turnover_mat_w_eq <- matrix(0, nrow = 31, ncol = 15)
turnover_mat_mv_shrinkage <- matrix(0, nrow = 31, ncol = 15)

to_BL_LP <- matrix(0, nrow = 31, ncol = 1)
to_BL_mkt <- matrix(0, nrow = 31, ncol = 1)
to_BL_eq <- matrix(0, nrow = 31, ncol = 1)
to_w_eq <- matrix(0, nrow = 31, ncol = 1)
to_mv_shrinkage <- matrix(0, nrow = 31, ncol = 1)


colnames(turnover_mat_BL_LP) <- colnames(return2[,1:15])
colnames(turnover_mat_BL_mkt) <- colnames(return2[,1:15])
colnames(turnover_mat_BL_eq) <- colnames(return2[,1:15])
colnames(turnover_mat_w_eq) <- colnames(return2[,1:15])
colnames(turnover_mat_mv_shrinkage) <- colnames(return2[,1:15])

for (t in 1:31) {
  for (j in 1:15) {
    tt <- t+1
    
    turnover_mat_BL_LP[t,j] <-  abs(opt_lp[tt,j] - w_plus_BL_LP[t,j]*100) 
    turnover_mat_BL_mkt[t,j] <-  abs(opt_mkt[tt,j] - w_plus_BL_mkt[t,j]*100) 
    turnover_mat_BL_eq[t,j] <-  abs(opt_eq[tt,j] - w_plus_BL_eq[t,j]*100) 
    turnover_mat_w_eq[t,j] <-  abs(w_equal2[tt,j]*100 - w_plus_w_eq[t,j]*100) 
    turnover_mat_mv_shrinkage[t,j] <-  abs(w_mv_shrinkage[tt,j] - w_plus_mv_shrikage[t,j]*100) 
  }
  
  to_BL_LP1[t,] <- sum(turnover_mat_BL_LP[t,])
  to_BL_mkt[t,] <- sum(turnover_mat_BL_mkt[t,])
  to_BL_eq[t,] <- sum(turnover_mat_BL_eq[t,])
  to_w_eq[t,] <- sum(turnover_mat_w_eq[t,])
  to_mv_shrinkage[t,] <- sum(turnover_mat_mv_shrinkage[t,])
}


#All thhe turnovers 
round(mean(to_BL_LP),3)
round(mean(to_BL_mkt),3)
round(mean(to_BL_eq),3)
round(mean(to_w_eq),3)
round(mean(to_mv_shrinkage),3)


#CEQ (certainty-equivalent)

realised_return_BL_LP <- c()
realised_return_BL_mkt <- c()
realised_return_BL_eq <- c()
realised_return_w_eq <- c()
realised_return_mv_shrinkage <- c()

for (i in 1:32) {
  
  tt <- i + 120 # One periode ahead compared to what has created the weights
  realised_return_BL_LP[i] <- as.matrix(exReturns.df[tt,1:15]) %*% as.vector(opt_lp[i,]/100)
  realised_return_BL_mkt[i] <- as.matrix(exReturns.df[tt,1:15]) %*% as.vector(opt_mkt[i,]/100)
  realised_return_BL_eq[i] <- as.matrix(exReturns.df[tt,1:15]) %*% as.vector(opt_eq[i,]/100)
  realised_return_w_eq[i] <- as.matrix(exReturns.df[tt,1:15]) %*% as.vector(w_equal2[i,])
  realised_return_mv_shrinkage[i] <- as.matrix(exReturns.df[tt,1:15]) %*% as.vector(w_mv_shrinkage[i,]/100)
  
}

lambda = 2.5  # risk aversion

CEQ_BL_LP <- mean(realised_return_BL_LP) - lambda/2 * sd(realised_return_BL_LP)^2
CEQ_BL_mkt <- mean(realised_return_BL_mkt) - lambda/2 * sd(realised_return_BL_mkt)^2
CEQ_BL_eq <- mean(realised_return_BL_eq) - lambda/2 * sd(realised_return_BL_eq)^2
CEQ_w_eq <- mean(realised_return_w_eq) - lambda/2 * sd(realised_return_w_eq)^2
CEQ_mv_shrinkage <- mean(realised_return_mv_shrinkage) - lambda/2 * sd(realised_return_mv_shrinkage)^2

#Return-loss
realized_dec <- all_realized/100
colnames(realized_dec) <- names
return_loss <- c()
for (i in 1:5) {
  
  nn <- names[i]
  return_loss[i] <- mean(realized_dec[,nn])/sd(realized_dec[,nn])*sd(realized_dec[,4]) - mean(realized_dec[,4])
  
}
round(return_loss*100,3)


##########################Views####################

#Views using EGARCH: 
library(rugarch)
library(tidyverse)

garch_spec = ugarchspec(variance.model=list(model="eGARCH", garchOrder=c(1,1), external.regressors =  cbind( as.matrix(return2$premium), as.matrix(return2$spread), as.matrix(return2$term),  as.matrix(return2$oli_price) )),
                        mean.model=list(armaOrder=c(0,0), archm = TRUE,
                        include.mean = TRUE, external.regressors = cbind( as.matrix(return2$premium), as.matrix(return2$spread))))


Danske.Aktier.bktest = ugarchroll(garch_spec, data = exReturns.df$Danske.Aktier, n.ahead = 1, 
                                  refit.every = 1, refit.window = "moving", n.start=120)

Globale.Aktier.bktest = ugarchroll(garch_spec, data = exReturns.df$Globale.Aktier, n.ahead = 1, 
                                   refit.every = 1, refit.window = "moving", n.start=120)

StabileAktier.bktest = ugarchroll(garch_spec, data = exReturns.df$StabileAktier, n.ahead = 1, 
                                  refit.every = 1, refit.window = "moving", n.start=120)

Emerging.market.bktest = ugarchroll(garch_spec, data = exReturns.df$Emerging.market, n.ahead = 1, 
                                    refit.every = 1, refit.window = "moving", n.start=120)

Indeksobligationer.bktest = ugarchroll(garch_spec, data = exReturns.df$Indeksobligationer, n.ahead = 1, 
                                       refit.every = 3, refit.window = "moving", n.start=120)

Statsobligationer.bktest = ugarchroll(garch_spec, data = exReturns.df$Statsobligationer, n.ahead = 1, 
                                      refit.every = 1, refit.window = "moving", n.start=120)

Realkredit.bktest = ugarchroll(garch_spec, data = exReturns.df$Realkredit, n.ahead = 1, 
                               refit.every = 1, refit.window = "moving", n.start=120)

IGObligationer.bktest = ugarchroll(garch_spec, data = exReturns.df$IGObligationer, n.ahead = 1, 
                                   refit.every = 1, refit.window = "moving", n.start=120)

HYObligationer.bktest = ugarchroll(garch_spec, data = exReturns.df$HYObligationer, n.ahead = 1, 
                                   refit.every = 3, refit.window = "moving", n.start=120)

EMDHARD.bktest = ugarchroll(garch_spec, data = exReturns.df$EMDHARD, n.ahead = 1, 
                            refit.every = 1, refit.window = "moving", n.start=120)

EMDLocal.bktest = ugarchroll(garch_spec, data = exReturns.df$EMDLocal, n.ahead = 1, 
                             refit.every = 2, refit.window = "moving", n.start=120)

PE.bktest = ugarchroll(garch_spec, data = exReturns.df$PE, n.ahead = 1, 
                       refit.every = 1, refit.window = "moving", n.start=120)

Infrastructure.bktest = ugarchroll(garch_spec, data = exReturns.df$Infrastructure, n.ahead = 1, 
                                   refit.every = 1, refit.window = "moving", n.start=120)

Skov.bktest = ugarchroll(garch_spec, data = exReturns.df$Skov, n.ahead = 1, 
                         refit.every = 1, refit.window = "moving", n.start=120)

RealEstate.bktest = ugarchroll(garch_spec, data = exReturns.df$RealEstate, n.ahead = 1, 
                               refit.every = 1, refit.window = "moving", n.start=120)


forecastMU1 <- as.data.frame(Danske.Aktier.bktest@forecast[["density"]][["Mu"]])
forecastMU2 <- as.data.frame(Globale.Aktier.bktest@forecast[["density"]][["Mu"]])
forecastMU3 <- as.data.frame(StabileAktier.bktest@forecast[["density"]][["Mu"]])
forecastMU4 <- as.data.frame(Emerging.market.bktest@forecast[["density"]][["Mu"]])
forecastMU5 <- as.data.frame(Indeksobligationer.bktest@forecast[["density"]][["Mu"]])
forecastMU6 <- as.data.frame(Statsobligationer.bktest@forecast[["density"]][["Mu"]])
forecastMU7 <- as.data.frame(Realkredit.bktest@forecast[["density"]][["Mu"]])
forecastMU8 <- as.data.frame(IGObligationer.bktest@forecast[["density"]][["Mu"]])
forecastMU9 <- as.data.frame(HYObligationer.bktest@forecast[["density"]][["Mu"]])
forecastMU10 <- as.data.frame(EMDHARD.bktest@forecast[["density"]][["Mu"]])
forecastMU11 <- as.data.frame(EMDLocal.bktest@forecast[["density"]][["Mu"]])
forecastMU12 <- as.data.frame(PE.bktest@forecast[["density"]][["Mu"]])
forecastMU13 <- as.data.frame(Infrastructure.bktest@forecast[["density"]][["Mu"]])
forecastMU14 <- as.data.frame(Skov.bktest@forecast[["density"]][["Mu"]])
forecastMU15 <- as.data.frame(RealEstate.bktest@forecast[["density"]][["Mu"]])

forecastSigma1 <- as.data.frame(Danske.Aktier.bktest@forecast[["density"]][["Sigma"]])
forecastSigma2 <- as.data.frame(Globale.Aktier.bktest@forecast[["density"]][["Sigma"]])
forecastSigma3 <- as.data.frame(StabileAktier.bktest@forecast[["density"]][["Sigma"]])
forecastSigma4 <- as.data.frame(Emerging.market.bktest@forecast[["density"]][["Sigma"]])
forecastSigma5 <- as.data.frame(Indeksobligationer.bktest@forecast[["density"]][["Sigma"]])
forecastSigma6 <- as.data.frame(Statsobligationer.bktest@forecast[["density"]][["Sigma"]])
forecastSigma7 <- as.data.frame(Realkredit.bktest@forecast[["density"]][["Sigma"]])
forecastSigma8 <- as.data.frame(IGObligationer.bktest@forecast[["density"]][["Sigma"]])
forecastSigma9 <- as.data.frame(HYObligationer.bktest@forecast[["density"]][["Sigma"]])
forecastSigma10 <- as.data.frame(EMDHARD.bktest@forecast[["density"]][["Sigma"]])
forecastSigma11 <- as.data.frame(EMDLocal.bktest@forecast[["density"]][["Sigma"]])
forecastSigma12 <- as.data.frame(PE.bktest@forecast[["density"]][["Sigma"]])
forecastSigma13 <- as.data.frame(Infrastructure.bktest@forecast[["density"]][["Sigma"]])
forecastSigma14 <- as.data.frame(Skov.bktest@forecast[["density"]][["Sigma"]])
forecastSigma15 <- as.data.frame(RealEstate.bktest@forecast[["density"]][["Sigma"]])

forecastsigma <- cbind(forecastSigma1, forecastSigma2, forecastSigma3, forecastSigma4, forecastSigma5, forecastSigma6, forecastSigma7, forecastSigma8, forecastSigma9, forecastSigma10,
                       forecastSigma11, forecastSigma12, forecastSigma13, forecastSigma14, forecastSigma15)

forecastsigma<- as.data.frame(forecastsigma)
colnames(forecastsigma) <- c("Danske.Aktier", "Globale.Aktier", "StabileAktier", "Emerging.market", "Indeksobligationer", 
                             'Statsobligationer', 'Realkredit', 'IGObligationer', 'HYObligationer', 
                             'EMDHARD', 'EMDLocal', 'PE', 'Infrastructure', 'Skov', 'RealEstate')


forecast<- cbind(forecastMU1,forecastMU2, forecastMU3, forecastMU4, forecastMU5, forecastMU6, forecastMU7, forecastMU8, forecastMU9, forecastMU10, forecastMU11, forecastMU12, forecastMU13, forecastMU14, forecastMU15)
forcast<- as.data.frame(forecast)
colnames(forcast) <- c("Danske.Aktier", "Globale.Aktier", "StabileAktier", "Emerging.market", "Indeksobligationer", 
                       'Statsobligationer', 'Realkredit', 'IGObligationer', 'HYObligationer', 
                       'EMDHARD', 'EMDLocal', 'PE', 'Infrastructure', 'Skov', 'RealEstate')
