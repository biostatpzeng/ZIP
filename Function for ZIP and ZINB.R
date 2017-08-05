

library(pscl)
library(MASS)
##########################################################
softrule=function(beta, lambda)
{
(lambda>=abs(beta))*0+
((lambda<abs(beta)) & (beta>0))*(beta-lambda)+
((lambda<abs(beta)) & (beta<0))*(beta+lambda)
}
##########################################################

###### direct method with coordinate descent
lmzip=function(x, y, lambda)
{
x=x
y=y
n=dim(x)[1]
p=dim(x)[2]
weight=as.vector(1/abs(glm(y~x-1)$coeff))
lambda1=lambda
lambda2=lambda1*weight
maxstep=min(n, p)*500
beta=matrix(NA, maxstep+1, p)
beta[1, ]=(glm(y~x-1)$coef)
delta=0.1
K=1
while((delta>1e-10) & (K<maxstep))
{
K=K+1
beta.temp=beta[K-1, ]
for (j in 1:p)
{
xminusj=x[, -j]
bminusj=beta.temp[-j]
yminusj=xminusj%*%bminusj
rminusj=y-yminusj
index=((j%%(p/2))!=1)
bj=softrule(sum(x[, j]*rminusj), lambda=lambda2[j]*index)/sum(x[, j]^2)
beta.temp[j]=bj
}
beta[K, ]=beta.temp
delta=max(abs(beta[K, ]-beta[K-1, ]))
}
beta=beta[K, ]
beta=as.matrix(beta)
if(is.null(colnames(x))){colnames(x)=c(paste("x", 1:p, sep=""))}
rownames(beta)=c(colnames(x))
beta=cbind(beta)
norm1=sum(abs(beta[2:(p/2)]))
norm2=sum(abs(beta[(p/2+2):p]))
norm3=norm1+norm2
object=list(beta=beta, lambda=lambda, norm=cbind(norm1, norm2, norm3), K=K, delta=delta)
}


########adaptive lasso for zero-inflated poisson
laszip=function(dataset, lambda)
{
dataset=dataset
lambda=lambda
zip=zeroinfl(y~.|., data=dataset, dist="poisson")
beta0=c((zip$coef)$count, (zip$coef)$zero)
p=dim(dataset)[2]
covb=vcov(zip)
sigma=solve(covb)
spectrumd=eigen(sigma)
lam=spectrumd$values
V=spectrumd$vectors
sigma12=V%*%diag(sqrt(lam), nrow=p*2, ncol=p*2)%*%t(V)
colnames=colnames(covb)
xstar=sigma12
colnames(xstar)=colnames(covb)
ystar=sigma12%*%as.vector(beta0)
fit=lmzip(xstar, ystar, lambda=lambda)
beta=fit$beta
norm=fit$norm
K=fit$K
delta=fit$delta
object=list(beta=beta, lambda=lambda, norm=norm, K=K, delta=delta)
}


library(pscl)
zeronb=function (formula,  data,  subset,  na.action,  weights,  
    dist = c("poisson",  "negbin",  "geometric"),  link = c("logit",  
        "probit",  "cloglog",  "cauchit",  "log"),  control = zeroinfl.control(...),  
    model = TRUE,  y = TRUE,  x = FALSE,  ...) 
{
    ziPoisson <- function(parms) {
        mu <- as.vector(exp(X %*% parms[1:kx]))
        phi <- as.vector(linkinv(Z %*% parms[(kx + 1):(kx + kz)]))
        loglik0 <- log(phi + exp(log(1 - phi) - mu))
        loglik1 <- log(1 - phi) + dpois(Y,  lambda = mu,  log = TRUE)
        loglik <- sum(weights[Y0] * loglik0[Y0]) + sum(weights[Y1] * 
            loglik1[Y1])
        loglik
    }
    ziNegBin <- function(parms) {
        mu <- as.vector(exp(X %*% parms[1:kx]))
        phi <- as.vector(linkinv(Z %*% parms[(kx + 1):(kx + kz)] ))
        theta <- exp(parms[(kx + kz) + 1])
        loglik0 <- log(phi + exp(log(1 - phi) + suppressWarnings(dnbinom(0,  
            size = theta,  mu = mu,  log = TRUE))))
        loglik1 <- log(1 - phi) + suppressWarnings(dnbinom(Y,  
            size = theta,  mu = mu,  log = TRUE))
        loglik <- sum(weights[Y0] * loglik0[Y0]) + sum(weights[Y1] * 
            loglik1[Y1])
        loglik
    }
    ziGeom <- function(parms) ziNegBin(c(parms,  0))
    gradPoisson <- function(parms) {
        eta <- as.vector(X %*% parms[1:kx])
        mu <- exp(eta)
        etaz <- as.vector(Z %*% parms[(kx + 1):(kx + kz)])
        muz <- linkinv(etaz)
        clogdens0 <- -mu
        dens0 <- muz * (1 - as.numeric(Y1)) + exp(log(1 - muz) + 
            clogdens0)
        wres_count <- ifelse(Y1,  Y - mu,  -exp(-log(dens0) + log(1 - 
            muz) + clogdens0 + log(mu)))
        wres_zero <- ifelse(Y1,  -1/(1 - muz) * linkobj$mu.eta(etaz),  
            (linkobj$mu.eta(etaz) - exp(clogdens0) * linkobj$mu.eta(etaz))/dens0)
        colSums(cbind(wres_count * weights * X,  wres_zero * weights * 
            Z))
    }
    gradGeom <- function(parms) {
        eta <- as.vector(X %*% parms[1:kx])
        mu <- exp(eta)
        etaz <- as.vector(Z %*% parms[(kx + 1):(kx + kz)])
        muz <- linkinv(etaz)
        clogdens0 <- dnbinom(0,  size = 1,  mu = mu,  log = TRUE)
        dens0 <- muz * (1 - as.numeric(Y1)) + exp(log(1 - muz) + 
            clogdens0)
        wres_count <- ifelse(Y1,  Y - mu * (Y + 1)/(mu + 1),  -exp(-log(dens0) + 
            log(1 - muz) + clogdens0 - log(mu + 1) + log(mu)))
        wres_zero <- ifelse(Y1,  -1/(1 - muz) * linkobj$mu.eta(etaz),  
            (linkobj$mu.eta(etaz) - exp(clogdens0) * linkobj$mu.eta(etaz))/dens0)
        colSums(cbind(wres_count * weights * X,  wres_zero * weights * 
            Z))
    }
    gradNegBin <- function(parms) {
        eta <- as.vector(X %*% parms[1:kx])
        mu <- exp(eta)
        etaz <- as.vector(Z %*% parms[(kx + 1):(kx + kz)])
        muz <- linkinv(etaz)
        theta <- exp(parms[(kx + kz) + 1])
        clogdens0 <- dnbinom(0,  size = theta,  mu = mu,  log = TRUE)
        dens0 <- muz * (1 - as.numeric(Y1)) + exp(log(1 - muz) + 
            clogdens0)
        wres_count <- ifelse(Y1,  Y - mu * (Y + theta)/(mu + theta),  
            -exp(-log(dens0) + log(1 - muz) + clogdens0 + log(theta) - 
                log(mu + theta) + log(mu)))
        wres_zero <- ifelse(Y1,  -1/(1 - muz) * linkobj$mu.eta(etaz),  
            (linkobj$mu.eta(etaz) - exp(clogdens0) * linkobj$mu.eta(etaz))/dens0)
        wres_theta <- theta * ifelse(Y1,  digamma(Y + theta) - 
            digamma(theta) + log(theta) - log(mu + theta) + 1 - 
            (Y + theta)/(mu + theta),  exp(-log(dens0) + log(1 - 
            muz) + clogdens0) * (log(theta) - log(mu + theta) + 
            1 - theta/(mu + theta)))
        colSums(cbind(wres_count * weights * X,  wres_zero * weights * 
            Z,  wres_theta))
    }
    dist <- match.arg(dist)
    loglikfun <- switch(dist,  poisson = ziPoisson,  geometric = ziGeom,  
        negbin = ziNegBin)
    gradfun <- switch(dist,  poisson = gradPoisson,  geometric = gradGeom,  
        negbin = gradNegBin)
    linkstr <- match.arg(link)
    linkobj <- make.link(linkstr)
    linkinv <- linkobj$linkinv
    if (control$trace) 
        cat("Zero-inflated Count Model\n",  paste("count model:",  
            dist,  "with log link\n"),  paste("zero-inflation model: binomial with",  
            linkstr,  "link\n"),  sep = "")
    cl <- match.call()
    if (missing(data)) 
        data <- environment(formula)
    mf <- match.call(expand.dots = FALSE)
    m <- match(c("formula",  "data",  "subset",  "na.action",  "weights"),  names(mf),  0)
    mf <- mf[c(1,  m)]
    mf$drop.unused.levels <- TRUE
    if (length(formula[[3]]) > 1 && identical(formula[[3]][[1]],  
        as.name("|"))) {
        ff <- formula
        formula[[3]][1] <- call("+")
        mf$formula <- formula
        ffc <- . ~ .
        ffz <- ~.
        ffc[[2]] <- ff[[2]]
        ffc[[3]] <- ff[[3]][[2]]
        ffz[[3]] <- ff[[3]][[3]]
        ffz[[2]] <- NULL
    }
    else {
        ffz <- ffc <- ff <- formula
        ffz[[2]] <- NULL
    }
    if (inherits(try(terms(ffz),  silent = TRUE),  "try-error")) {
        ffz <- eval(parse(text = sprintf(paste("%s -",  deparse(ffc[[2]])),  
            deparse(ffz))))
    }
    mf[[1]] <- as.name("model.frame")
    mf <- eval(mf,  parent.frame())
    mt <- attr(mf,  "terms")
    mtX <- terms(ffc,  data = data)
    X <- model.matrix(mtX,  mf)
    mtZ <- terms(ffz,  data = data)
    mtZ <- terms(update(mtZ,  ~.),  data = data)
    Z <- model.matrix(mtZ,  mf)
    Y <- model.response(mf,  "numeric")
    if (length(Y) < 1) 
        stop("empty model")
    if (all(Y > 0)) 
        stop("invalid dependent variable,  minimum count is not zero")
    if (!isTRUE(all.equal(as.vector(Y),  as.integer(round(Y + 
        0.001))))) 
        stop("invalid dependent variable,  non-integer values")
    Y <- as.integer(round(Y + 0.001))
    if (any(Y < 0)) 
        stop("invalid dependent variable,  negative counts")
    if (control$trace) {
        cat("dependent variable:\n")
        tab <- table(factor(Y,  levels = 0:max(Y)),  exclude = NULL)
        names(dimnames(tab)) <- NULL
        print(tab)
    }
    n <- length(Y)
    kx <- NCOL(X)
    kz <- NCOL(Z)
    Y0 <- Y <= 0
    Y1 <- Y > 0
    weights <- model.weights(mf)
    if (is.null(weights)) 
        weights <- 1
    if (length(weights) == 1) 
        weights <- rep.int(weights,  n)
    weights <- as.vector(weights)
    names(weights) <- rownames(mf)
    start <- control$start
    if (!is.null(start)) {
        valid <- TRUE
        if (!("count" %in% names(start))) {
            valid <- FALSE
            warning("invalid starting values,  count model coefficients not specified")
            start$count <- rep.int(0,  kx)
        }
        if (!("zero" %in% names(start))) {
            valid <- FALSE
            warning("invalid starting values,  zero-inflation model coefficients not specified")
            start$zero <- rep.int(0,  kz)
        }
        if (length(start$count) != kx) {
            valid <- FALSE
            warning("invalid starting values,  wrong number of count model coefficients")
        }
        if (length(start$zero) != kz) {
            valid <- FALSE
            warning("invalid starting values,  wrong number of zero-inflation model coefficients")
        }
        if (dist == "negbin") {
            if (!("theta" %in% names(start))) 
                start$theta <- 1
            start <- list(count = start$count,  zero = start$zero,  
                theta = as.vector(start$theta[1]))
        }
        else {
            start <- list(count = start$count,  zero = start$zero)
        }
        if (!valid) 
            start <- NULL
    }
    if (is.null(start)) {
        if (control$trace) 
            cat("generating starting values...")
        model_count <- glm.fit(X,  Y,  family = poisson(),  weights = weights)
        model_zero <- glm.fit(Z,  as.integer(Y0),  weights = weights,  
            family = binomial(link = linkstr))
        start <- list(count = model_count$coefficients,  zero = model_zero$coefficients)
        if (dist == "negbin") 
            start$theta <- 1
        if (control$EM & dist == "poisson") {
            mui <- model_count$fitted
            probi <- model_zero$fitted
            probi <- probi/(probi + (1 - probi) * dpois(0,  mui))
            probi[Y1] <- 0
            ll_new <- loglikfun(c(start$count,  start$zero))
            ll_old <- 2 * ll_new
            while (abs((ll_old - ll_new)/ll_old) > control$reltol) {
                ll_old <- ll_new
                model_count <- glm.fit(X,  Y,  weights = weights * 
                  (1 - probi),  family = poisson(),  
                  start = start$count)
                model_zero <- suppressWarnings(glm.fit(Z,  probi,  
                  weights = weights, family = binomial(link = linkstr),  
                  start = start$zero))
                mui <- model_count$fitted
                probi <- model_zero$fitted
                probi <- probi/(probi + (1 - probi) * dpois(0,  
                  mui))
                probi[Y1] <- 0
                start <- list(count = model_count$coefficients,  
                  zero = model_zero$coefficients)
                ll_new <- loglikfun(c(start$count,  start$zero))
            }
        }
        if (control$EM & dist == "geometric") {
            mui <- model_count$fitted
            probi <- model_zero$fitted
            probi <- probi/(probi + (1 - probi) * dnbinom(0,  
                size = 1,  mu = mui))
            probi[Y1] <- 0
            ll_new <- loglikfun(c(start$count,  start$zero))
            ll_old <- 2 * ll_new
            if (!require("MASS")) {
                ll_old <- ll_new
                warning("EM estimation of starting values not available")
            }
            while (abs((ll_old - ll_new)/ll_old) > control$reltol) {
                ll_old <- ll_new
                model_count <- suppressWarnings(glm.fit(X,  Y,  
                  weights = weights * (1 - probi),  
                  family = negative.binomial(1),  start = start$count))
                model_zero <- suppressWarnings(glm.fit(Z,  probi,  
                  weights = weights,  family = binomial(link = linkstr),  
                  start = start$zero))
                start <- list(count = model_count$coefficients,  
                  zero = model_zero$coefficients)
                mui <- model_count$fitted
                probi <- model_zero$fitted
                probi <- probi/(probi + (1 - probi) * dnbinom(0,  
                  size = 1,  mu = mui))
                probi[Y1] <- 0
                ll_new <- loglikfun(c(start$count,  start$zero))
            }
        }
        if (control$EM & dist == "negbin") {
            mui <- model_count$fitted
            probi <- model_zero$fitted
            probi <- probi/(probi + (1 - probi) * dnbinom(0,  
                size = start$theta,  mu = mui))
            probi[Y1] <- 0
            ll_new <- loglikfun(c(start$count,  start$zero,  log(start$theta)))
            ll_old <- 2 * ll_new
            if (!require("MASS")) {
                ll_old <- ll_new
                warning("EM estimation of starting values not available")
            }
           
            while (abs((ll_old - ll_new)/ll_old) > control$reltol) {
                ll_old <- ll_new
                model_count <- suppressWarnings(glm.nb(Y ~ 0 + 
                  X ,  weights = weights * (1 - 
                  probi),  start = start$count,  init.theta = start$theta))
                model_zero <- suppressWarnings(glm.fit(Z,  probi,  
                  weights = weights,   family = binomial(link = linkstr),  
                  start = start$zero))
                start <- list(count = model_count$coefficients,  
                  zero = model_zero$coefficients,  theta = model_count$theta)
                mui <- model_count$fitted
                probi <- model_zero$fitted
                probi <- probi/(probi + (1 - probi) * dnbinom(0,  
                  size = start$theta,  mu = mui))
                probi[Y1] <- 0
                ll_new <- loglikfun(c(start$count,  start$zero,  
                  log(start$theta)))
            }
        }
        if (control$trace) 
            cat("done\n")
    }
    if (control$trace) 
        cat("calling optim() for ML estimation:\n")
    method <- control$method
    hessian <- control$hessian
    ocontrol <- control
    control$method <- control$hessian <- control$EM <- control$start <- NULL
    fit <- optim(fn = loglikfun,  gr = gradfun,  par = c(start$count,  
        start$zero,  if (dist == "negbin") log(start$theta) else NULL),  
        method = method,  hessian = hessian,  control = control)
    if (fit$convergence > 0) 
        warning("optimization failed to converge")
    coefc <- fit$par[1:kx]
    names(coefc) <- names(start$count) <- colnames(X)
    coefz <- fit$par[(kx + 1):(kx + kz)]
    names(coefz) <- names(start$zero) <- colnames(Z)
    vc <- -solve(as.matrix(fit$hessian))
    zimcov<- -solve(as.matrix(fit$hessian))
    zimhessian<- as.matrix(fit$hessian)
    if (dist == "negbin") {
        np <- kx + kz + 1
        theta <- as.vector(exp(fit$par[np]))
        SE.logtheta <- as.vector(sqrt(diag(vc)[np]))
        vc <- vc[-np,  -np,  drop = FALSE]
    }
    else {
        theta <- NULL
        SE.logtheta <- NULL
    }
    colnames(vc) <- rownames(vc) <- c(paste("count",  colnames(X),  
        sep = "_"),  paste("zero",  colnames(Z),  sep = "_"))
    mu <- exp(X %*% coefc )[,  1]
    phi <- linkinv(Z %*% coefz)[,  1]
    Yhat <- (1 - phi) * mu
    res <- sqrt(weights) * (Y - Yhat)
    nobs <- sum(weights > 0)
    rval <- list(coefficients = list(count = coefc,  zero = coefz), 
    zimcov=zimcov, zimhessian=zimhessian, 
        residuals = res,  fitted.values = Yhat,  optim = fit,  method = method,  
        control = ocontrol,  start = start,  weights = if (identical(as.vector(weights),  
            rep.int(1L,  n))) NULL else weights, 
        terms = list(count = mtX,  zero = mtZ,  full = mt),  theta = theta,  
        SE.logtheta = SE.logtheta,  loglik = fit$value,  vcov = vc,  
        dist = dist,  link = linkstr,  linkinv = linkinv,  converged = fit$convergence < 
            1,  call = cl,  formula = ff,  levels = .getXlevels(mt,  
            mf),  contrasts = list(count = attr(X,  "contrasts"),  
            zero = attr(Z,  "contrasts")))
    if (model) 
        rval$model <- mf
    if (y) 
        rval$y <- Y
    if (x) 
        rval$x <- list(count = X,  zero = Z)
    class(rval) <- "zeroinfl"
    return(rval)
}


##########################################################
softrule=function(beta, lambda)
{(lambda>=abs(beta))*0+
((lambda<abs(beta)) & (beta>0))*(beta-lambda)+
((lambda<abs(beta)) & (beta<0))*(beta+lambda)}
##########################################################


###### direct method with coordinate descent
lmzinb=function(x, y, lambda)
{
x=x
y=y
n=dim(x)[1]
p=dim(x)[2]
weight=as.vector(1/abs(glm(y~x-1)$coeff))
lambda1=lambda
lambda2=lambda1*weight
maxstep=min(n, p)*500
beta=matrix(NA, maxstep+1, p)
beta[1, ]=glm(y~x-1)$coef
delta=0.001
K=1
while((delta>1e-10) & (K<maxstep))
{
K=K+1
beta.temp=beta[K-1, ]
for (j in 1:p)
{
xminusj=x[, -j]
bminusj=beta.temp[-j]
yminusj=xminusj%*%bminusj
rminusj=y-yminusj
if ((j==1) | (j==(p+1)/2) | (j==p))
{bj=softrule(sum(x[, j]*rminusj), lambda=0)/sum(x[, j]^2)}
else 
{bj=softrule(sum(x[, j]*rminusj), lambda=lambda2[j])/sum(x[, j]^2)}
beta.temp[j]=bj
}
beta[K, ]=beta.temp
delta=max(abs(beta[K, ]-beta[K-1, ]))
}
beta=beta[K, ]
beta=as.matrix(beta)
if(is.null(colnames(x))){colnames(x)=c(paste("x", 1:p, sep=""))}
rownames(beta)=c(colnames(x))
beta=cbind(beta)
norm1=sum(abs(beta[2:((p+1)/2-1)]))
norm2=sum(abs(beta[((p+1)/2+1):(p-1)]))
norm3=norm1+norm2
object=list(beta=beta, lambda=lambda, norm=cbind(norm1, norm2, norm3), K=K, delta=delta)
}




########adaptive lasso for zero-inflated negative binomial 
laszinb=function(dataset, lambda)
{
dataset=dataset
lambda=lambda
zinb=zeronb(y~.|., data=dataset, dist="negbin")
p=dim(dataset)[2]
names0=c("inter", colnames(dataset[, -p]))
beta0=cbind(c((zinb$coef)$count, (zinb$coef)$zero, log(alpha0=1/(zinb$theta))))
rownames(beta0)=c(paste("count", names0, sep=""), paste("zero", names0, sep=""), "loga")
covb=zinb$zimcov
colnames(covb)=rownames(covb)=rownames(beta0)
sigma=solve(covb)
spectrumd=eigen(sigma)
lam=spectrumd$values
V=spectrumd$vectors
sigma12=V%*%diag(sqrt(lam), nrow=p*2+1, ncol=p*2+1)%*%t(V)
xstar=sigma12
colnames(xstar)=colnames(covb)
ystar=sigma12%*%as.vector(beta0)
fit=lmzinb(xstar, ystar, lambda=lambda)
beta=fit$beta
norm=fit$norm
K=fit$K
delta=fit$delta
object=list(beta=beta, lambda=lambda, norm=norm, K=K, delta=delta)
}


