library(Matrix)
library(MASS)
library(matrixStats)

Regression <- function(x, y, intercept=TRUE, loss=c("ls", "ml", "lpre")){
  if(intercept){x <- cbind(1, x)}
  x <- as.matrix(x)
  if(loss=="ls"){
    # fit <- lm(y~x+0)
    # beta <- coef(fit)
    beta <- solve(t(x) %*% x, tol=1e-100) %*% t(x) %*% y
    # SVD <- svd(x)
    # beta <- SVD$v %*% diag(1/SVD$d^2) %*% t(SVD$v) %*% t(x) %*% y
  }
  
  if(loss=="ml"){
    SQN <- function(x, y, beta0){
      # Negative log likelihood function
      F.function <- function(belta, x, y){
        f <- sum(log(1 + exp(x %*% belta))) - t(y) %*% x %*% belta
        return(f)
      }
      
      # Derivate of the negative log likelihood function about beta
      DF.function <- function(belta, x, y){
        pw <- numeric(length(y))
        for(i in 1:length(y)){
          pw[i] <- 1/(1 + exp(-sum(x[i,] * belta)))
        }
        fd <- t(x) %*% (pw-y) 
        return(fd)
      }
      
      maxoutiter = 20
      #maxiniter = 20
      stoprule = 0.01
      # maxoutiter = 300
      # maxiniter = 30
      # stoprule = 0.001
      yita=0.4; rho=0.55;
      Hk=diag(ncol(x))
      outiter=0
      repeat{
        gk=DF.function(beta0,x,y)
        if(sqrt(sum(gk^2))< stoprule | outiter > maxoutiter) break   ##belta=beltao
        dk=-Hk%*%gk
        initer=0; mk=0;outiter1=0
        repeat{
          beltanew=beta0 + rho^initer*dk
          newPNLL=F.function(beltanew, x, y)
          oldPNLL=F.function(beta0, x, y)
          temp=yita*(rho^initer)*sum(gk*dk)
          mk=initer
          initer=initer+1
          if(newPNLL<(oldPNLL+temp)||outiter1>5000) break
          outiter1=outiter1+1
        }
        ##======== DFP==========##
        belta=beta0+(rho^mk)*dk
        ##--------- update Hk----------##
        sk=belta-beta0     ##displacement shift
        yk=DF.function(belta,x,y)-gk   ##gradient shift
        if(sum(sk*yk)>0) Hk=Hk-(Hk%*%(yk%*%t(yk))%*%Hk)/as.numeric(t(yk)%*%Hk%*%yk)+(sk%*%t(sk))/as.numeric(t(sk)%*%yk)
        outiter=outiter+1
        beta0=belta
      }
      return(beta0)
    }
    beta <- SQN(x, y, rep(0, ncol(x)))
  }
  
  if(loss=="lpre"){
    bk_fun <- function(x, y){
      x <- as.matrix(x)
      y <- as.vector(y)
      tx <- t(x)
      yinv <- 1/y
      
      # SVD <- svd(x)
      # par <- SVD$v %*% diag(1/SVD$d^2) %*% t(SVD$v) %*% t(x) %*% log(y)
      
      par <- solve(t(x) %*% x, tol=1e-100) %*% tx %*% log(y) #coef(lm(log(y)~x+0)) #rep(0, ncol(x))
      b.est <- par+100
      for(k in 1:1000){
        f <- tx %*% (yinv * exp(x %*% par) - y*exp(-x %*% par)) #一阶导数
        tt <- yinv*exp(x %*% par)+y*exp(-x %*% par) 
        f_diff <- matrix(0, ncol(x), ncol(x))
        for (i in 1:length(y)) {
          f_diff <- f_diff + as.matrix(x[i, ]) %*% tx[, i] * tt[i] 
        }
        
        # SVD <- svd(f_diff)
        # b.est <- par - SVD$v %*% diag(1/SVD$d) %*% t(SVD$u) %*% f
        
        b.est <- par-solve(f_diff, tol=1e-100) %*% f
        if(norm(b.est - par,"2")<=1e-4) break
        par <- b.est
      }
      return(b.est)
    }
    beta <- bk_fun(x, y)
  }
  
  return(beta)
}

epdas <- function(x, y, size=NULL, intercept=TRUE, tau=0.5, loss=c("ls", "ml", "lpre")){
  x0 <- as.matrix(x)
  y0 <- as.matrix(y)
  np <- dim(x0)
  N <- np[1]
  p <- np[2]
  
  nmachine <- 1
  ##Define sample on each machine
  if(nmachine==1){
    n <- N
    groups <- list()
    groups[[1]] <- 1:N
  }else{
    n <- trunc(N/nmachine)
    o <- 1:N
    groups <- vector("list", nmachine)
    for (j in 1:(nmachine - 1)) {
      jj <- (1 + (j - 1) * n)
      groups[[j]] <- (o[jj:(jj + n - 1)])
    }
    groups[[nmachine]] <- o[(1 + (nmachine - 1) * n):N]
  }
  
  tx0 <- t(x0)
  tx02 <- t(x0^2)
  yinv0 <- 1/y0
  
  
  x <- x0[groups[[1]], ]
  y <- y0[groups[[1]]]
  yinv <- 1/y
  tx <- t(x)
  tx2 <- t(x^2)
  
  
  if(is.null(size)) {size <- unique(floor(seq(1, n/(log(n)*log(p)), length=20)))}
  
  if(intercept){
    b0 <- switch(loss, ls=mean(y), ml=coef(glm(y~1, family=binomial(link="logit"))), lpre=log(prod(y^(1/n))))
  }else{
    b0 <- 0
  }
  
  opt.model <- function(x0, y0, par, nmachine, loss){
    par <- as.matrix(par)
    pre <- rep(0, ncol(par))
    for (j in 1:nmachine) {
      x0j <- x0[groups[[j]], ] 
      y0j <- y0[groups[[j]]]
      pe0j <- x0j %*% par[-1, ] + par[1, ]
      prej <- switch (loss,
                      ls = colSums((y0j - pe0j)^2),
                      ml = -2*colSums((y0j * pe0j - log(1+exp(pe0j)))),
                      lpre = colSums((y0j - exp(pe0j))^2/(y0j*exp(pe0j)))
      )
      pre <- pre + prej
    }
    an <- log(log(N)) * log(p) * size/N
    
    hbic <- switch (loss,
                    ls = log(pre/N) + an,
                    ml = pre/N + an,
                    lpre = log(pre/N) + an
    )
    
    return(list(opt_beta=par[, which.min(hbic)], opt_ms=size[which.min(hbic)]))
  }
  
  
  Gradient <- function(x0, y0, par, nmachine, loss=c("ls", "ml", "lpre")){
    # Note that length(beta)-ncol(x)=1
    Astar <- which(par[-1]!=0)
    gj <- dj <- Matrix(0L, nrow=p, ncol = nmachine)
    for (j in 1:nmachine) {
      x0j <- x0[groups[[j]], ] 
      tx0j <- tx0[, groups[[j]]]
      tx02j <- tx02[, groups[[j]]]
      y0j <- y0[groups[[j]]]
      yinv0j <- yinv0[groups[[j]]]
      pej <- as.matrix(x0j[, Astar]) %*% par[Astar+1] + par[1]
      gj[, j] <- switch(loss, 
                        ls = rowSums(tx02j),
                        ml = tx02j %*% (1/(2 + exp(-pej) + exp(pej))),
                        lpre= tx02j %*% (yinv0j * exp(pej) + y0j*exp(-pej)))
      
      dj[, j] <- switch(loss, 
                        ls = tx0j %*% (y0j - pej), 
                        ml = tx0j %*% (y0j - 1/(1+exp(-pej))),
                        lpre = -tx0j %*% (yinv0j * exp(pej) - y0j*exp(-pej)))
    }
    
    
    return(list(gk=rowSums(gj), dk=rowSums(dj)/rowSums(gj)))
  }
  
  Hession_matrix <- function(x, y, Astar, par, intercept, loss){
    if(intercept){
      xx <- cbind(1, x[, Astar])
      pe <- xx %*% par
    }else{
      xx <- as.matrix(x[, Astar])
      par <- c(0, par)
      pe <- xx %*% par[-1]
    }
    
    if(loss=="ls"){
      hess <- t(xx) %*% xx
    }else if(loss=="ml"){
      gd <- 1/(2 + exp(-pe) + exp(pe))
      hess <- matrix(0, length(Astar)+intercept, length(Astar)+intercept)
      for (i in 1:length(y)) {
        hess <- hess + as.matrix(xx[i, ]) %*% t(xx[i, ]) * gd[i]
      }
      
    }else{
      yinv <- 1/y
      gd <- yinv*exp(pe) + y*exp(-pe)
      hess <- matrix(0, length(Astar)+intercept, length(Astar)+intercept)
      for (i in 1:length(y)) {
        hess <- hess + as.matrix(xx[i, ]) %*% t(xx[i, ]) * gd[i] 
      }
    }
    return(hess)
  }
  
  dcbk_fun <- function(x0, y0, Astar, intercept, nmachine){
    t.start <- proc.time()
    grad <- matrix(0, length(Astar)+intercept, 1)
    hess <- matrix(0, length(Astar)+intercept, length(Astar)+intercept)
    time1 <- proc.time()
    for (j in 1:nmachine) {
      estij <- Regression(x0[groups[[j]], Astar], y0[groups[[j]]], intercept=intercept, loss=loss)
      hessj <- Hession_matrix(x, y, Astar, estij, intercept, loss)
      grad <- grad + hessj %*% estij
      hess <- hess + hessj
    }
    time2 <- proc.time()
    # SVD <- svd(hess)
    # b.est <- SVD$v %*% diag(1/SVD$d) %*% t(SVD$u) %*% grad
    
    b.est <- solve(hess,tol=1e-60) %*% grad
    t.end <- proc.time()
    running.time <- (t.end-t.start)[3] - (nmachine-1)*(time2-time1)[3]/nmachine
    if(!intercept){b.est <- c(0, b.est)}
    return(list(beta=b.est, running_time=running.time))
  }
  
  
  dc_epdas <- function(ms, loss){
    time.start <- proc.time()
    res_iter <- Matrix(0L, nrow=p+3, ncol=1)
    res_iter[3] <- b0
    t1 <- proc.time()
    grad <- Gradient(x0, y0, res_iter[3:(p+3)], nmachine, loss=loss)
    t2 <- proc.time()
    time.grad <- (t2 - t1)[3]
    gk <- grad$gk
    dk <- grad$dk
    Hk <- sqrt(gk)*abs(tau*res_iter[4:(p+3)] + (1-tau)*dk)
    Ak <- which(Hk >= sort(Hk, decreasing =TRUE)[ms])
    tk <- tdc <- 0
    maxoutiter <- min(2*ms, 20)
    for (k in 1:maxoutiter) {
      Ik <- setdiff(1:p, Ak)
      res_iter[Ik+3] <- 0
      tk1 <- proc.time()
      fit <- dcbk_fun(x0, y0, Astar=Ak, intercept=intercept, nmachine=nmachine)
      tk2 <- proc.time()
      tk <- (tk2-tk1)[3] + tk
      tdc <- fit$running_time + tdc
      
      res_iter[Ak+3] <- fit$beta[-1]
      res_iter[3] <- fit$beta[1]
      
      t1 <- proc.time()
      grad <- Gradient(x0, y0, res_iter[3:(p+3)], nmachine, loss=loss)
      t2 <- proc.time()
      time.grad <- time.grad + (t2 - t1)[3]
      gk <- grad$gk
      dk <- grad$dk
      Hk <- sqrt(gk)*abs(tau*res_iter[4:(p+3)] + (1-tau)*dk)
      Anew <- which(Hk >= sort(Hk, decreasing =TRUE)[ms])
      if(setequal(Ak, Anew)){
        time.end <- proc.time()
        rt <- (time.end - time.start)[3] - tk + tdc - time.grad*(1-1/nmachine)
        res_iter[1:2] <- c(rt, k+1)
        return(res_iter)
      }
      Ak <- Anew
    }
    time.end <- proc.time()
    rt <- (time.end - time.start)[3] - tk + tdc - time.grad*(1-1/nmachine)
    res_iter[1:2] <- c(rt, k+1)
    return(res_iter)
  }
  
  
  para_beta <- lapply(size, function(ms){dc_epdas(ms, loss=loss)})
  para_beta <- do.call(cbind, para_beta)
  running_time <- para_beta[1, ]
  iter <- para_beta[2, ]
  beta <- para_beta[-(1:2), ]
  tunning <- opt.model(x0, y0, beta, nmachine, loss)
  
  
  return(list(beta=beta, size=size, iter=iter, running=running_time, opt_beta=tunning$opt_beta, opt_ms=tunning$opt_ms))
}

depdas <- function(x, y, size=NULL, intercept=TRUE, tau=0.5, 
                   nmachine=5, loss=c("ls", "ml", "lpre"), A0=FALSE){
  x0 <- as.matrix(x)
  y0 <- as.matrix(y)
  np <- dim(x0)
  N <- np[1]
  p <- np[2]
  
  
  ##Define sample on each machine
  if(nmachine==1){
    n <- N
    groups <- list()
    groups[[1]] <- 1:N
  }else{
    n <- trunc(N/nmachine)
    o <- 1:N
    groups <- vector("list", nmachine)
    for (j in 1:(nmachine - 1)) {
      jj <- (1 + (j - 1) * n)
      groups[[j]] <- (o[jj:(jj + n - 1)])
    }
    groups[[nmachine]] <- o[(1 + (nmachine - 1) * n):N]
  }
  
  tx0 <- t(x0)
  tx02 <- t(x0^2)
  yinv0 <- 1/y0
  
  
  x <- x0[groups[[1]], ]
  y <- y0[groups[[1]]]
  yinv <- 1/y
  tx <- t(x)
  tx2 <- t(x^2)
  
  
  if(is.null(size)) {size <- unique(floor(seq(1, n/(log(n)*log(p)), length=20)))}
  
  if(intercept){
    b0 <- switch(loss, ls=mean(y), ml=coef(glm(y~1, family=binomial(link="logit"))), lpre=log(prod(y^(1/n))))
  }else{
    b0 <- 0
  }
  
  opt.model <- function(x0, y0, par, nmachine, loss){
    par <- as.matrix(par)
    pre <- rep(0, ncol(par))
    for (j in 1:nmachine) {
      x0j <- x0[groups[[j]], ] 
      y0j <- y0[groups[[j]]]
      pe0j <- x0j %*% par[-1, ] + par[1, ]
      prej <- switch (loss,
                      ls = colSums((y0j - pe0j)^2),
                      ml = -2*colSums((y0j * pe0j - log(1+exp(pe0j)))),
                      lpre = colSums((y0j - exp(pe0j))^2/(y0j*exp(pe0j)))
      )
      pre <- pre + prej
    }
    an <- log(log(N)) * log(p) * size/N
    
    hbic <- switch (loss,
                    ls = log(pre/N) + an,
                    ml = pre/N + an,
                    lpre = log(pre/N) + an
    )
    
    return(list(opt_beta=par[, which.min(hbic)], opt_ms=size[which.min(hbic)]))
  }
  
  
  Gradient <- function(x0, y0, par, nmachine, loss=c("ls", "ml", "lpre")){
    # Note that length(beta)-ncol(x)=1
    Astar <- which(par[-1]!=0)
    gj <- dj <- Matrix(0L, nrow=p, ncol = nmachine)
    for (j in 1:nmachine) {
      x0j <- x0[groups[[j]], ] 
      tx0j <- tx0[, groups[[j]]]
      tx02j <- tx02[, groups[[j]]]
      y0j <- y0[groups[[j]]]
      yinv0j <- yinv0[groups[[j]]]
      pej <- as.matrix(x0j[, Astar]) %*% par[Astar+1] + par[1]
      gj[, j] <- switch(loss, 
                        ls = rowSums(tx02j),
                        ml = tx02j %*% (1/(2 + exp(-pej) + exp(pej))),
                        lpre= tx02j %*% (yinv0j * exp(pej) + y0j*exp(-pej)))
      
      dj[, j] <- switch(loss, 
                        ls = tx0j %*% (y0j - pej), 
                        ml = tx0j %*% (y0j - 1/(1+exp(-pej))),
                        lpre = -tx0j %*% (yinv0j * exp(pej) - y0j*exp(-pej)))
    }
    
    
    return(list(gk=rowSums(gj), dk=rowSums(dj)/rowSums(gj)))
  }
  
  Hession_matrix <- function(x, y, Astar, par, intercept, loss){
    if(intercept){
      xx <- cbind(1, x[, Astar])
      pe <- xx %*% par
    }else{
      xx <- as.matrix(x[, Astar])
      par <- c(0, par)
      pe <- xx %*% par[-1]
    }
    
    if(loss=="ls"){
      hess <- t(xx) %*% xx
    }else if(loss=="ml"){
      gd <- 1/(2 + exp(-pe) + exp(pe))
      hess <- matrix(0, length(Astar)+intercept, length(Astar)+intercept)
      for (i in 1:length(y)) {
        hess <- hess + as.matrix(xx[i, ]) %*% t(xx[i, ]) * gd[i]
      }
      
    }else{
      yinv <- 1/y
      gd <- yinv*exp(pe) + y*exp(-pe)
      hess <- matrix(0, length(Astar)+intercept, length(Astar)+intercept)
      for (i in 1:length(y)) {
        hess <- hess + as.matrix(xx[i, ]) %*% t(xx[i, ]) * gd[i] 
      }
    }
    return(hess)
  }
  
  dcbk_fun <- function(x0, y0, Astar, intercept, nmachine){
    t.start <- proc.time()
    grad <- matrix(0, length(Astar)+intercept, 1)
    hess <- matrix(0, length(Astar)+intercept, length(Astar)+intercept)
    time1 <- proc.time()
    for (j in 1:nmachine) {
      estij <- Regression(x0[groups[[j]], Astar], y0[groups[[j]]], intercept=intercept, loss=loss)
      hessj <- Hession_matrix(x, y, Astar, estij, intercept, loss)
      grad <- grad + hessj %*% estij
      hess <- hess + hessj
    }
    time2 <- proc.time()
    # SVD <- svd(hess)
    # b.est <- SVD$v %*% diag(1/SVD$d) %*% t(SVD$u) %*% grad
    
    b.est <- solve(hess,tol=1e-60) %*% grad
    t.end <- proc.time()
    running.time <- (t.end-t.start)[3] - (nmachine-1)*(time2-time1)[3]/nmachine
    if(!intercept){b.est <- c(0, b.est)}
    return(list(beta=b.est, running_time=running.time))
  }
  
  
  dc_epdas <- function(ms, loss){
    if(A0==FALSE||nmachine==1){
      time.start <- proc.time()
      res_iter <- Matrix(0L, nrow=p+3, ncol=1)
      res_iter[3] <- b0
      t1 <- proc.time()
      grad <- Gradient(x0, y0, res_iter[3:(p+3)], nmachine, loss=loss)
      t2 <- proc.time()
      time.grad <- (t2 - t1)[3]
      gk <- grad$gk
      dk <- grad$dk
      Hk <- sqrt(gk)*abs(tau*res_iter[4:(p+3)] + (1-tau)*dk)
      Ak <- which(Hk >= sort(Hk, decreasing =TRUE)[ms])
      tk <- tdc <- 0
    }else{
      time.start <- proc.time()
      fit <- epdas(x, y, size=ms, intercept=intercept, tau=tau, loss=loss)
      res_iter <- Matrix(0L, nrow=p+3, ncol=1)
      Ak <- which(fit$beta[-1]!=0)
      tk <- tdc <- time.grad <- 0
    }
    
    maxoutiter <- min(2*ms, 20)
    for (k in 1:maxoutiter) {
      Ik <- setdiff(1:p, Ak)
      res_iter[Ik+3] <- 0
      tk1 <- proc.time()
      fit <- dcbk_fun(x0, y0, Astar=Ak, intercept=intercept, nmachine=nmachine)
      tk2 <- proc.time()
      tk <- (tk2-tk1)[3] + tk
      tdc <- fit$running_time + tdc
      
      res_iter[Ak+3] <- fit$beta[-1]
      res_iter[3] <- fit$beta[1]
      
      t1 <- proc.time()
      grad <- Gradient(x0, y0, res_iter[3:(p+3)], nmachine, loss=loss)
      t2 <- proc.time()
      time.grad <- time.grad + (t2 - t1)[3]
      gk <- grad$gk
      dk <- grad$dk
      Hk <- sqrt(gk)*abs(tau*res_iter[4:(p+3)] + (1-tau)*dk)
      Anew <- which(Hk >= sort(Hk, decreasing =TRUE)[ms])
      if(setequal(Ak, Anew)){
        time.end <- proc.time()
        rt <- (time.end - time.start)[3] - tk + tdc - time.grad*(1-1/nmachine)
        res_iter[1:2] <- c(rt, k+!A0)
        return(res_iter)
      }
      Ak <- Anew
    }
    time.end <- proc.time()
    rt <- (time.end - time.start)[3] - tk + tdc - time.grad*(1-1/nmachine)
    res_iter[1:2] <- c(rt, k+!A0)
    return(res_iter)
  }
  
  
  para_beta <- lapply(size, function(ms){dc_epdas(ms, loss=loss)})
  para_beta <- do.call(cbind, para_beta)
  running_time <- para_beta[1, ]
  iter <- para_beta[2, ]
  beta <- para_beta[-(1:2), ]
  tunning <- opt.model(x0, y0, beta, nmachine, loss)
  
  
  return(list(beta=beta, size=size, iter=iter, running=running_time, opt_beta=tunning$opt_beta, opt_ms=tunning$opt_ms))
}

lcdepdas <- function(x, y, size=NULL, intercept=TRUE, tau=0.5, 
                     nmachine=5, loss=c("ls", "ml", "lpre"), A0=FALSE){
  x0 <- as.matrix(x)
  y0 <- as.matrix(y)
  np <- dim(x0)
  N <- np[1]
  p <- np[2]
  
  
  ##Define sample on each machine
  if(nmachine==1){
    n <- N
    groups <- list()
    groups[[1]] <- 1:N
  }else{
    n <- trunc(N/nmachine)
    o <- 1:N
    groups <- vector("list", nmachine)
    for (j in 1:(nmachine - 1)) {
      jj <- (1 + (j - 1) * n)
      groups[[j]] <- (o[jj:(jj + n - 1)])
    }
    groups[[nmachine]] <- o[(1 + (nmachine - 1) * n):N]
  }
  
  tx0 <- t(x0)
  tx02 <- t(x0^2)
  yinv0 <- 1/y0
  
  
  x <- x0[groups[[1]], ]
  y <- y0[groups[[1]]]
  yinv <- 1/y
  tx <- t(x)
  tx2 <- t(x^2)
  
  
  if(is.null(size)) {size <- seq(1, floor(n/(log(n)*log(p))), 1)}
  
  if(intercept){
    b0 <- switch(loss, ls=mean(y), ml=coef(glm(y~1, family=binomial(link="logit"))), lpre=log(prod(y^(1/n))))
  }else{
    b0 <- 0
  }
  
  opt.model <- function(x0, y0, par, nmachine, loss){
    par <- as.matrix(par)
    pre <- rep(0, ncol(par))
    for (j in 1:nmachine) {
      x0j <- x0[groups[[j]], ] 
      y0j <- y0[groups[[j]]]
      pe0j <- x0j %*% par[-1, ] + par[1, ]
      prej <- switch (loss,
                      ls = colSums((y0j - pe0j)^2),
                      ml = -2*colSums((y0j * pe0j - log(1+exp(pe0j)))),
                      lpre = colSums((y0j - exp(pe0j))^2/(y0j*exp(pe0j)))
      )
      pre <- pre + prej
    }
    an <- log(log(N)) * log(p) * size/N
    
    hbic <- switch (loss,
                    ls = log(pre/N) + an,
                    ml = pre/N + an,
                    lpre = log(pre/N) + an
    )
    
    return(list(opt_beta=par[, which.min(hbic)], opt_ms=size[which.min(hbic)]))
  }
  
  RF_Astar <- function(x0, y0, beta, ms, loss=c("ls", "ml", "lpre")){
    Aesti <- NULL
    for (j in 1:nmachine) {
      gradj <- Gradient(j, x0, y0, beta, loss)
      gj <- gradj$gk
      dj <- gradj$dk
      Hj <- sqrt(gj)*abs(tau*beta[-1] + (1-tau)*dj)
      Aesti <- c(Aesti, which(Hj >= sort(Hj, decreasing =TRUE)[ms]))
    }
    as.numeric(names(sort(table(Aesti), decreasing = TRUE)[1:ms]))
  }
  
  
  Gradient <- function(j, x0, y0, par, loss=c("ls", "ml", "lpre")){
    # Note that length(beta)-ncol(x)=1
    Astar <- which(par[-1]!=0)
    x0j <- x0[groups[[j]], ] 
    tx0j <- tx0[, groups[[j]]]
    tx02j <- tx02[, groups[[j]]]
    y0j <- y0[groups[[j]]]
    yinv0j <- yinv0[groups[[j]]]
    pej <- as.matrix(x0j[, Astar]) %*% par[Astar+1] + par[1]
    gj <- switch(loss, 
                 ls = rowSums(tx02j),
                 ml = tx02j %*% (1/(2 + exp(-pej) + exp(pej))),
                 lpre= tx02j %*% (yinv0j * exp(pej) + y0j*exp(-pej)))
    
    dj <- switch(loss, 
                 ls = tx0j %*% (y0j - pej), 
                 ml = tx0j %*% (y0j - 1/(1+exp(-pej))),
                 lpre = -tx0j %*% (yinv0j * exp(pej) - y0j*exp(-pej)))
    
    
    return(list(gk=gj, dk=dj/gj))
  }
  
  
  
  
  Hession_matrix <- function(x, y, Astar, par, intercept, loss){
    if(intercept){
      xx <- cbind(1, x[, Astar])
      pe <- xx %*% par
    }else{
      xx <- as.matrix(x[, Astar])
      par <- c(0, par)
      pe <- xx %*% par[-1] 
    }
    
    if(loss=="ls"){
      hess <- t(xx) %*% xx
    }else if(loss=="ml"){
      gd <- 1/(2 + exp(-pe) + exp(pe))
      hess <- matrix(0, length(Astar)+intercept, length(Astar)+intercept)
      for (i in 1:length(y)) {
        hess <- hess + as.matrix(xx[i, ]) %*% t(xx[i, ]) * gd[i]
      }
      
    }else{
      yinv <- 1/y
      gd <- yinv*exp(pe) + y*exp(-pe)
      hess <- matrix(0, length(Astar)+intercept, length(Astar)+intercept)
      for (i in 1:length(y)) {
        hess <- hess + as.matrix(xx[i, ]) %*% t(xx[i, ]) * gd[i] 
      }
    }
    return(hess)
  }
  
  dcbk_fun <- function(x0, y0, Astar, intercept, nmachine){
    t.start <- proc.time()
    grad <- matrix(0, length(Astar)+intercept, 1)
    hess <- matrix(0, length(Astar)+intercept, length(Astar)+intercept)
    time1 <- proc.time()
    for (j in 1:nmachine) {
      estij <- Regression(x0[groups[[j]], Astar], y0[groups[[j]]], intercept=intercept, loss=loss)
      hessj <- Hession_matrix(x, y, Astar, estij, intercept, loss)
      grad <- grad + hessj %*% estij
      hess <- hess + hessj
    }
    time2 <- proc.time()
    # SVD <- svd(hess)
    # b.est <- SVD$v %*% diag(1/SVD$d) %*% t(SVD$u) %*% grad
    
    b.est <- solve(hess,tol=1e-60) %*% grad
    t.end <- proc.time()
    running.time <- (t.end-t.start)[3] - (nmachine-1)*(time2-time1)[3]/nmachine
    if(!intercept){b.est <- c(0, b.est)}
    return(list(beta=b.est, running_time=running.time))
  }
  
  dc_epdas <- function(ms, loss){
    if(A0==FALSE||nmachine==1){
      time.start <- proc.time()
      res_iter <- Matrix(0L, nrow=p+3, ncol=1)
      res_iter[3] <- b0
      tak <- 0
      t1ak <- proc.time()
      Ak <- RF_Astar(x0, y0, res_iter[3:(p+3)], ms, loss)
      t2ak <- proc.time()
      tak <- tak + (t2ak - t1ak)[3]
      tk <- tdc <- 0
    }else{
      time.start <- proc.time()
      fit <- epdas(x, y, size=ms, intercept=intercept, tau=tau, loss=loss)
      res_iter <- Matrix(0L, nrow=p+3, ncol=1)
      tak <- 0
      Ak <- which(fit$beta[-1]!=0)
      tk <- tdc <- 0
    }
    
    maxoutiter <- min(2*ms, 20)
    for (k in 1:maxoutiter) {
      Ik <- setdiff(1:p, Ak)
      res_iter[Ik+3] <- 0
      
      tk1 <- proc.time()
      fit <- dcbk_fun(x0, y0, Astar=Ak, intercept=intercept, nmachine=nmachine)
      tk2 <- proc.time()
      tk <- (tk2-tk1)[3] + tk
      tdc <- fit$running_time + tdc
      
      res_iter[Ak+3] <- fit$beta[-1]
      res_iter[3] <- fit$beta[1]
      t1ak <- proc.time()
      Anew <- RF_Astar(x0, y0, res_iter[3:(p+3)], ms, loss)
      t2ak <- proc.time()
      tak <- tak + (t2ak-t1ak)[3]
      
      if(setequal(Ak, Anew)){
        time.end <- proc.time()
        rt <- (time.end - time.start)[3] - tk + tdc - tak*(1-1/nmachine)
        res_iter[1:2] <- c(rt, k+!A0)
        return(res_iter)
      }
      Ak <- Anew
    }
    time.end <- proc.time()
    rt <- (time.end - time.start)[3] - tk + tdc  - tak*(1-1/nmachine)
    res_iter[1:2] <- c(rt, k+!A0)
    return(res_iter)
  }
  
  
  para_beta <- lapply(size, function(ms){dc_epdas(ms, loss=loss)})
  para_beta <- do.call(cbind, para_beta)
  running_time <- para_beta[1, ]
  iter <- para_beta[2, ]
  beta <- para_beta[-(1:2), ]
  tunning <- opt.model(x0, y0, beta, nmachine, loss)
  
  
  return(list(beta=beta, size=size, iter=iter, running=running_time, opt_beta=tunning$opt_beta, opt_ms=tunning$opt_ms))
}
